package distsys

import (
	"bytes"
	"container/list"
	"encoding/gob"
	"errors"
	"fmt"
	"io"
	"log"
	"net"
	"sync"
	"time"

	"github.com/benbjohnson/immutable"
)

// Here is a warning from go-static-check:
// error var CriticalSectionAborted should have name of the form ErrFoo (ST1012)
var CriticalSectionAborted = errors.New("MPCal critical section aborted")

type ArchetypeResource interface {
	// I suggest removing these two lines, because it makes a very strong dependency to Gob library which is hard to change in future.
	// We can use an approach similar to the Codec that Go's RPC server uses to be flexible in serialization method.
	gob.GobDecoder
	gob.GobEncoder
	Abort() chan struct{}
	PreCommit() chan error
	Commit() chan struct{}
	ReadValue() (TLAValue, error)
	WriteValue(value TLAValue) error
	Index(index TLAValue) (ArchetypeResource, error)
}

type ArchetypeResourceLeafMixin struct{}

var ArchetypeResourceLeafIndexedError = errors.New("internal error: attempted to index a leaf archetype resource")

func (ArchetypeResourceLeafMixin) Index(TLAValue) (ArchetypeResource, error) {
	return nil, ArchetypeResourceLeafIndexedError
}

type ArchetypeResourceMapMixin struct{}

var ArchetypeResourceMapReadWriteError = errors.New("internal error: attempted to read/write a map archetype resource")

func (ArchetypeResourceMapMixin) ReadValue() (TLAValue, error) {
	return TLAValue{}, ArchetypeResourceMapReadWriteError
}

func (ArchetypeResourceMapMixin) WriteValue(TLAValue) error {
	return ArchetypeResourceMapReadWriteError
}

////////////////////////////////////////////////
////         ARCHETYPE RESOURCES            ////
////////////////////////////////////////////////

// A bare-bones resource: just holds and buffers a TLAValue
// --------------------------------------------------------

type LocalArchetypeResource struct {
	ArchetypeResourceLeafMixin
	record localArchetypeResourceRecord
}

type localArchetypeResourceRecord struct {
	IsInitialized bool // start-up flag, to avoid setting up state again when reloading from disk
	HasOldValue   bool // if true, this resource has already been written in this critical section
	// if this resource is already written in this critical section, OldValue contains prev value
	// Value always contains the "current" value
	Value, OldValue TLAValue
}

var _ ArchetypeResource = &LocalArchetypeResource{}

func EnsureLocalArchetypeResource(ensurer MPCalContextResourceEnsurer, value TLAValue) ArchetypeResourceHandle {
	return ensurer(&LocalArchetypeResource{}, func(resource ArchetypeResource) {
		res := resource.(*LocalArchetypeResource)
		if !res.record.IsInitialized {
			res.record.IsInitialized = true
			res.record.Value = value
		}
	})
}

func (res *LocalArchetypeResource) Abort() chan struct{} {
	if res.record.HasOldValue {
		res.record.Value = res.record.OldValue
		res.record.HasOldValue = false
		res.record.OldValue = TLAValue{}
	}
	return nil
}

func (res *LocalArchetypeResource) PreCommit() chan error {
	return nil
}

func (res *LocalArchetypeResource) Commit() chan struct{} {
	res.record.HasOldValue = false
	res.record.OldValue = TLAValue{}
	return nil
}

func (res *LocalArchetypeResource) ReadValue() (TLAValue, error) {
	return res.record.Value, nil
}

func (res *LocalArchetypeResource) WriteValue(value TLAValue) error {
	if !res.record.HasOldValue {
		res.record.OldValue = res.record.Value
		res.record.HasOldValue = true
	}
	res.record.Value = value
	return nil
}

func (res *LocalArchetypeResource) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	return decoder.Decode(&res.record)
}

func (res *LocalArchetypeResource) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(&res.record)
	if err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// Input channel resource: a read-only data source backed by an externally-controlled Go channel
// ---------------------------------------------------------------------------------------------

type InputChannelResource struct {
	ArchetypeResourceLeafMixin
	channel <-chan TLAValue
	buffer  []TLAValue
}

var _ ArchetypeResource = &InputChannelResource{}

func EnsureInputChannelResource(ensurer MPCalContextResourceEnsurer, channel <-chan TLAValue) ArchetypeResourceHandle {
	return ensurer(&InputChannelResource{}, func(resource ArchetypeResource) {
		res := resource.(*InputChannelResource)
		res.channel = channel
	})
}

func (res *InputChannelResource) Abort() chan struct{} {
	return nil
}

func (res *InputChannelResource) PreCommit() chan error {
	return nil
}

func (res *InputChannelResource) Commit() chan struct{} {
	res.buffer = nil
	return nil
}

func (res *InputChannelResource) ReadValue() (TLAValue, error) {
	if len(res.buffer) > 0 {
		value := res.buffer[0]
		res.buffer = res.buffer[1:]
		return value, nil
	}

	select {
	case value := <-res.channel:
		res.buffer = append(res.buffer, value)
		return value, nil
	case <-time.After(time.Millisecond * 20):
		return TLAValue{}, CriticalSectionAborted
	}
}

func (res *InputChannelResource) WriteValue(value TLAValue) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *InputChannelResource) GobDecode(input []byte) error {
	panic("implement me")
}

func (res *InputChannelResource) GobEncode() ([]byte, error) {
	panic("implement me")
}

// Output channel resource: a write-only resource backed by an externally-readable Go channel
// ------------------------------------------------------------------------------------------

type OutputChannelResource struct {
	ArchetypeResourceLeafMixin
	channel chan<- TLAValue
	buffer  []TLAValue
}

var _ ArchetypeResource = &OutputChannelResource{}

func EnsureOutputChannelResource(ensurer MPCalContextResourceEnsurer, channel chan<- TLAValue) ArchetypeResourceHandle {
	return ensurer(&OutputChannelResource{}, func(resource ArchetypeResource) {
		res := resource.(*OutputChannelResource)
		res.channel = channel
	})
}

func (res *OutputChannelResource) Abort() chan struct{} {
	res.buffer = nil
	return nil
}

func (res *OutputChannelResource) PreCommit() chan error {
	return nil
}

func (res *OutputChannelResource) Commit() chan struct{} {
	ch := make(chan struct{})
	go func() {
		for _, value := range res.buffer {
			res.channel <- value
		}
		res.buffer = nil
		ch <- struct{}{}
	}()
	return ch
}

func (res *OutputChannelResource) ReadValue() (TLAValue, error) {
	panic(fmt.Errorf("attempted to read from an input channel resource"))
}

func (res *OutputChannelResource) WriteValue(value TLAValue) error {
	res.buffer = append(res.buffer, value)
	return nil
}

func (res *OutputChannelResource) GobDecode(i []byte) error {
	panic("implement me")
}

func (res *OutputChannelResource) GobEncode() ([]byte, error) {
	panic("implement me")
}

// A generic map resource, with hooks to programmatically and serializably realize child resources during execution
// ----------------------------------------------------------------------------------------------------------------

type IncrementalArchetypeMapResource struct {
	ArchetypeResourceMapMixin
	realizedMap  *immutable.Map
	FillFunction func(IncrementalArchetypeMapResourceEnsurer, TLAValue)
}

type incrementalArchetypeMapResourceRecord struct {
	Key   TLAValue
	Value ArchetypeResource
}

type IncrementalArchetypeMapResourceEnsurer func(blank ArchetypeResource, configFn func(ArchetypeResource))

var _ ArchetypeResource = &IncrementalArchetypeMapResource{}

func EnsureIncrementalArchetypeMapResource(ensurer MPCalContextResourceEnsurer, fillFunction func(IncrementalArchetypeMapResourceEnsurer, TLAValue)) ArchetypeResourceHandle {
	return ensurer(&IncrementalArchetypeMapResource{}, func(resource ArchetypeResource) {
		resource.(*IncrementalArchetypeMapResource).EnsureConfig(fillFunction)
	})
}

func (res *IncrementalArchetypeMapResource) EnsureConfig(fillFunction func(IncrementalArchetypeMapResourceEnsurer, TLAValue)) {
	if res.realizedMap == nil {
		res.realizedMap = immutable.NewMap(TLAValueHasher{})
	}
	// this should only happen once, because, once it happens, FillFunction will be set.
	// this structure allows sub-resources to set up any static non-serializable information, if they have just
	// previously been deserialized.
	if res.FillFunction == nil {
		res.FillFunction = fillFunction
		it := res.realizedMap.Iterator()
		for !it.Done() {
			key, value := it.Next()
			fillFunction(func(_ ArchetypeResource, configFn func(ArchetypeResource)) {
				configFn(value.(ArchetypeResource))
			}, key.(TLAValue))
		}
	}
}

func (res *IncrementalArchetypeMapResource) Index(index TLAValue) (ArchetypeResource, error) {
	var resource ArchetypeResource
	res.FillFunction(func(blank ArchetypeResource, configFn func(ArchetypeResource)) {
		if subRes, ok := res.realizedMap.Get(index); ok {
			resource = subRes.(ArchetypeResource)
		} else {
			configFn(blank)
			res.realizedMap = res.realizedMap.Set(index, blank)
			resource = blank
		}
	}, index)
	return resource, nil
}

func (res *IncrementalArchetypeMapResource) PreCommit() chan error {
	var nonTrivialPreCommits []chan error
	it := res.realizedMap.Iterator()
	for !it.Done() {
		_, subRes := it.Next()
		ch := subRes.(ArchetypeResource).PreCommit()
		if ch != nil {
			nonTrivialPreCommits = append(nonTrivialPreCommits, ch)
		}
	}
	if len(nonTrivialPreCommits) == 0 {
		return nil
	}
	outCh := make(chan error)
	go func() {
		var err error
		for _, ch := range nonTrivialPreCommits {
			err = <-ch
			if err != nil {
				break
			}
		}
		outCh <- err
	}()
	return outCh
}

func (res *IncrementalArchetypeMapResource) Commit() chan struct{} {
	var nonTrivialCommits []chan struct{}
	it := res.realizedMap.Iterator()
	for !it.Done() {
		_, subRes := it.Next()
		ch := subRes.(ArchetypeResource).Commit()
		if ch != nil {
			nonTrivialCommits = append(nonTrivialCommits, ch)
		}
	}
	if len(nonTrivialCommits) == 0 {
		return nil
	}
	outCh := make(chan struct{})
	go func() {
		for _, ch := range nonTrivialCommits {
			<-ch
		}
		outCh <- struct{}{}
	}()
	return outCh
}

func (res *IncrementalArchetypeMapResource) Abort() chan struct{} {
	var nonTrivialAborts []chan struct{}
	it := res.realizedMap.Iterator()
	for !it.Done() {
		_, subRes := it.Next()
		ch := subRes.(ArchetypeResource).Abort()
		if ch != nil {
			nonTrivialAborts = append(nonTrivialAborts, ch)
		}
	}
	if len(nonTrivialAborts) == 0 {
		return nil
	}
	outCh := make(chan struct{})
	go func() {
		for _, ch := range nonTrivialAborts {
			<-ch
		}
		outCh <- struct{}{}
	}()
	return outCh
}

func (res *IncrementalArchetypeMapResource) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for {
		var record incrementalArchetypeMapResourceRecord
		err := decoder.Decode(&record)
		if err != nil {
			if errors.Is(err, io.EOF) {
				res.realizedMap = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(record.Key, record.Value)
	}
}

func (res *IncrementalArchetypeMapResource) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := res.realizedMap.Iterator()
	for !it.Done() {
		key, value := it.Next()
		err := encoder.Encode(incrementalArchetypeMapResourceRecord{
			Key:   key.(TLAValue),
			Value: value.(ArchetypeResource),
		})
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

// Global State as Archetype Resource
// ----------------------------------

// TODO: recreate

// Mailboxes as Archetype Resource
// -------------------------------

type TCPMailboxesArchetypeResource struct {
	IncrementalArchetypeMapResource
}

const (
	tcpNetworkBegin = iota
	tcpNetworkValue
	tcpNetworkPreCommit
	tcpNetworkPreCommitAck
	tcpNetworkCommit
)

var _ ArchetypeResource = &TCPMailboxesArchetypeResource{}

type TCPMailboxKind int

const (
	TCPMailboxesLocal = iota
	TCPMailboxesRemote
)

func EnsureTCPMailboxesArchetypeResource(ensurer MPCalContextResourceEnsurer, addressMappingFn func(TLAValue) (TCPMailboxKind, string)) ArchetypeResourceHandle {
	return ensurer(&TCPMailboxesArchetypeResource{}, func(resource ArchetypeResource) {
		res := resource.(*TCPMailboxesArchetypeResource)
		res.EnsureConfig(func(ensurer IncrementalArchetypeMapResourceEnsurer, index TLAValue) {
			tpe, addr := addressMappingFn(index)
			switch tpe {
			case TCPMailboxesLocal:
				ensurer(&TCPMailboxLocalArchetypeResource{}, func(resource ArchetypeResource) {
					r := resource.(*TCPMailboxLocalArchetypeResource)
					r.EnsureConfig(addr)
				})
			case TCPMailboxesRemote:
				ensurer(&TCPMailboxRemoteArchetypeResource{}, func(resource ArchetypeResource) {
					r := resource.(*TCPMailboxRemoteArchetypeResource)
					r.EnsureConfig(addr)
				})
			default:
				panic(fmt.Errorf("invalid TCP mailbox type %d for address %s: expected local or remote, which are %d or %d", tpe, addr, TCPMailboxesLocal, TCPMailboxesRemote))
			}
		})
	})
}

type TCPMailboxLocalArchetypeResource struct {
	ArchetypeResourceLeafMixin
	listenAddr string

	listener         net.Listener
	buffer           *list.List
	bufferFillNotify chan struct{}
	bufferLock       sync.Mutex

	bufferSize int

	readBacklog     []TLAValue
	readsInProgress []TLAValue
}

var _ ArchetypeResource = &TCPMailboxLocalArchetypeResource{}

func (res *TCPMailboxLocalArchetypeResource) ensureSetup() {
	res.bufferLock.Lock()
	defer res.bufferLock.Unlock()

	if res.buffer == nil {
		res.buffer = list.New()
	}

	if res.bufferFillNotify == nil {
		// ideally, the notification count should be equal to buffer size, but, for reliability, we sometimes
		// store an oversize buffer. in this case, surreptitiously bump the channel size to avoid deadlock
		notifyCount := res.bufferSize
		if res.buffer.Len() > notifyCount {
			notifyCount = res.buffer.Len()
		}
		res.bufferFillNotify = make(chan struct{}, notifyCount)
		for i := 0; i < notifyCount; i++ {
			res.bufferFillNotify <- struct{}{}
		}
	}

	if res.listener == nil {
		var err error
		res.listener, err = net.Listen("tcp", res.listenAddr)
		if err != nil {
			log.Fatalf("could not listen on address %s", res.listenAddr)
		}
		go func() {
			for {
				conn, err := res.listener.Accept()
				if err != nil {
					log.Fatalf("error listening on %s", res.listenAddr)
				}
				go func() {
					var err error
					encoder := gob.NewEncoder(conn)
					decoder := gob.NewDecoder(conn)
					var localBuffer []TLAValue
					hasBegun := false
					for {
						if err != nil {
							log.Printf("network error: %s", err.Error())
							break
						}
						var tag int
						err = decoder.Decode(&tag)
						if err != nil {
							continue
						}
						switch tag {
						case tcpNetworkBegin:
							if localBuffer != nil {
								localBuffer = nil
							}
							hasBegun = true
						case tcpNetworkValue:
							var value TLAValue
							err = decoder.Decode(&value)
							if err != nil {
								continue
							}
							localBuffer = append(localBuffer, value)
						case tcpNetworkPreCommit:
							err = encoder.Encode(struct{}{})
							if err != nil {
								continue
							}
						case tcpNetworkCommit:
							// when crash-proofing, we need a way to identify repeat commits
							// _when an old commit was successful but didn't persist due to crash_
							// could be done by:
							// - send a unique incrementing counter on pre-commit
							// - commit-er sends this id on commit, and we store this commit attempt in a persistent set
							//   alongside the buffer itself
							// - receiving two commits for the same id can be detected by looking in the set, in which
							//   case do nothing and reply that the thing is done.
							// - starting a new critical section sends the id of the remote's last commit, which
							//   indicates that commit was successful, and that the id can be removed from the set
							if !hasBegun {
								err = encoder.Encode(true)
								if err != nil {
									continue
								}
							} else {
								func() {
									res.bufferLock.Lock()
									defer res.bufferLock.Unlock()
									// TODO: store buffer durably
									for _, val := range localBuffer {
										res.buffer.PushBack(val)
									}
									// store buffer as a locked structure, use channels to notify when important change happen
									// - when the channel becomes not-full, notify any potential writers
									// - when the channel becomes not-empty, notify the reader
								}()
								err = encoder.Encode(false)
								if err != nil {
									continue
								}
								hasBegun = false // TODO: also store durably?
								// push notifications _after_ the buffer has been filled, so we guarantee that
								// a filled version of the buffer has been atomically saved, while allowing
								// us to block for a long time without the complication of holding a lock on the buffer
								for range localBuffer {
									res.bufferFillNotify <- struct{}{}
								}
							}
						}
					}
					err = conn.Close()
					if err != nil {
						log.Printf("error closing connection: %s", err.Error())
					}
				}()
			}
		}()
	}
}

func (res *TCPMailboxLocalArchetypeResource) EnsureConfig(addr string) {
	res.listenAddr = addr
	res.ensureSetup()
}

func (res *TCPMailboxLocalArchetypeResource) Abort() chan struct{} {
	res.readBacklog = append(res.readBacklog, res.readsInProgress...)
	res.readsInProgress = nil
	return nil
}

func (res *TCPMailboxLocalArchetypeResource) PreCommit() chan error {
	return nil
}

func (res *TCPMailboxLocalArchetypeResource) Commit() chan struct{} {
	res.readsInProgress = nil
	return nil
}

func (res *TCPMailboxLocalArchetypeResource) ReadValue() (TLAValue, error) {
	// if a critical section previously aborted, already-read values will be here
	if len(res.readBacklog) > 0 {
		value := res.readBacklog[0]
		res.readBacklog[0] = TLAValue{}
		res.readBacklog = res.readBacklog[1:]
		return value, nil
	}

	// otherwise, either pull a notification + atomically read a value from the buffer, or time out
	select {
	case <-res.bufferFillNotify:
		res.bufferLock.Lock()
		defer res.bufferLock.Unlock()
		frontElem := res.buffer.Front()
		poppedValue := frontElem.Value.(TLAValue)
		res.buffer.Remove(frontElem)
		res.readsInProgress = append(res.readsInProgress, poppedValue)
		return poppedValue, nil
	case <-time.After(20 * time.Millisecond):
		return TLAValue{}, CriticalSectionAborted
	}
}

func (res *TCPMailboxLocalArchetypeResource) WriteValue(value TLAValue) error {
	panic(fmt.Errorf("attempted to write value %v to a local mailbox archetype resource", value))
}

func (res *TCPMailboxLocalArchetypeResource) GobDecode(i []byte) error {
	panic("implement me")
}

func (res *TCPMailboxLocalArchetypeResource) GobEncode() ([]byte, error) {
	panic("implement me")
}

type TCPMailboxRemoteArchetypeResource struct {
	ArchetypeResourceLeafMixin
	dialAddr string

	inCriticalSection bool
	conn              net.Conn
	connEncoder       *gob.Encoder
	connDecoder       *gob.Decoder
	sendBuffer        []TLAValue
}

var _ ArchetypeResource = &TCPMailboxRemoteArchetypeResource{}

func (res *TCPMailboxRemoteArchetypeResource) EnsureConfig(addr string) {
	res.dialAddr = addr
}

func (res *TCPMailboxRemoteArchetypeResource) ensureConnection() error {
	if res.conn == nil {
		var err error
		res.conn, err = net.Dial("tcp", res.dialAddr)
		if err != nil {
			log.Printf("failed to dial %s, aborting after 50ms: %v", res.dialAddr, err)
			time.Sleep(time.Millisecond * 50)
			return CriticalSectionAborted
		}
		res.connEncoder = gob.NewEncoder(res.conn)
		res.connDecoder = gob.NewDecoder(res.conn)
	}
	return nil
}

func (res *TCPMailboxRemoteArchetypeResource) Abort() chan struct{} {
	res.sendBuffer = nil
	// nothing to do; the remote end tolerates just starting over with no explanation
	return nil
}

func (res *TCPMailboxRemoteArchetypeResource) PreCommit() chan error {
	ch := make(chan error, 1)
	go func() {
		var err error
		{
			err = res.connEncoder.Encode(tcpNetworkPreCommit)
			if err != nil {
				goto handleError
			}
			var ack struct{}
			err = res.connDecoder.Decode(&ack)
			if err != nil {
				goto handleError
			}
			ch <- nil
			return
		}
	handleError:
		log.Printf("network error while performing pre-commit handshake, aborting: %v", err)
		res.conn = nil
		ch <- CriticalSectionAborted
	}()
	return ch
}

func (res *TCPMailboxRemoteArchetypeResource) Commit() chan struct{} {
	ch := make(chan struct{}, 1)
	go func() {
		var err error
	outerLoop:
		for {
			if err != nil {
				log.Printf("network error during commit, resetting: %v", err)
				res.conn = nil
			}
			err = res.ensureConnection()
			if err != nil {
				continue outerLoop
			}
			err = res.connEncoder.Encode(tcpNetworkCommit)
			if err != nil {
				continue outerLoop
			}
			var shouldResend bool
			err = res.connDecoder.Decode(&shouldResend)
			if err != nil {
				continue outerLoop
			}
			if shouldResend {
				err = res.connEncoder.Encode(tcpNetworkBegin)
				if err != nil {
					continue outerLoop
				}
				for _, value := range res.sendBuffer {
					err = res.connEncoder.Encode(tcpNetworkValue)
					if err != nil {
						continue outerLoop
					}
					err = res.connEncoder.Encode(&value)
					if err != nil {
						continue outerLoop
					}
				}
				continue outerLoop
			}
			res.sendBuffer = nil
			ch <- struct{}{}
			return
		}
	}()
	return ch
}

func (res *TCPMailboxRemoteArchetypeResource) ReadValue() (TLAValue, error) {
	panic(fmt.Errorf("attempted to read from a remote mailbox archetype resource"))
}

// I suggest writing a handleFunction instead of using goto.
func (res *TCPMailboxRemoteArchetypeResource) WriteValue(value TLAValue) error {
	err := res.ensureConnection()
	if err != nil {
		return err
	}
	if !res.inCriticalSection {
		err = res.connEncoder.Encode(tcpNetworkBegin)
		if err != nil {
			goto handleError
		}
	}
	err = res.connEncoder.Encode(tcpNetworkValue)
	if err != nil {
		goto handleError
	}
	err = res.connEncoder.Encode(&value)
	if err != nil {
		goto handleError
	}
	return nil
handleError:
	log.Printf("network error during remote value write, aborting: %v", err)
	res.conn = nil
	return CriticalSectionAborted
}

func (res *TCPMailboxRemoteArchetypeResource) GobDecode(i []byte) error {
	panic("implement me")
}

func (res *TCPMailboxRemoteArchetypeResource) GobEncode() ([]byte, error) {
	panic("implement me")
}
