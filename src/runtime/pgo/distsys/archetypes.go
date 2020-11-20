package distsys

import (
	"fmt"
	"io/ioutil"
	"net/rpc"
	"os"
	"path"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// ResourceAccess indicates what type of access the a caller is requesting.
type ResourceAccess int

// ResourceInternalError represents errros that happen when
// interacting with an archetype resource. When a
// ResourceInternalError is returned by a call to Acquire(), Read(),
// Write() or Release(), the error is propagated back to the caller.
type ResourceInternalError struct {
	cause string
}

func (err *ResourceInternalError) Error() string {
	return fmt.Sprintf("Internal error: %s", err.cause)
}

// AbortRetryError represents the situation where a failure has
// occurrred that prevents the system from making progress. The atomic
// step should be rolleback and tried again. If this error is returned
// by a call to Acquire(), Read() or Write(), the action will be
// retried.
type AbortRetryError struct {
	cause string
}

func (err *AbortRetryError) Error() string {
	return fmt.Sprintf("Abort and retry: %s", err.cause)
}

const (
	READ_ACCESS = iota + 1
	WRITE_ACCESS

	LOCK_NUM_RETRIES = 10
	LOCK_WAIT        = 20 // ms

	RPC_SUCCESS = iota
	MAILBOX_IS_FULL_ERROR
)

// priorities associated with each archetype resource implementation.
// Used to ensure acquisition happens in consistent order
var (
	priorityCounter uint64
	priorityMap     map[reflect.Type]uint64
)

func init() {
	atomic.StoreUint64(&priorityCounter, 0)
	priorityMap = map[reflect.Type]uint64{}

	// Register resources provided by the runtime
	RegisterResource(&GlobalVariable{})
	RegisterResource(&Mailbox{})
	RegisterResource(&LocalChannelResource{})
	RegisterResource(&FileResource{})
	RegisterResource(&ImmutableResource{})
	RegisterResource(&LocallySharedResource{})
	RegisterResource(&AtomicInteger{})
	RegisterResource(&SleepResource{})
}

// RegisterResource assigns a priority to the type of the resource
// passed.  Calling this function more than once for the same resource
// type is an error.
func RegisterResource(resource interface{}) {
	resourceType := reflect.TypeOf(resource).Elem()

	if _, exists := priorityMap[resourceType]; exists {
		panic(fmt.Sprintf("Resource type already registered: %T", resource))
	}

	priorityMap[reflect.TypeOf(resource).Elem()] = atomic.AddUint64(&priorityCounter, 1)
}

// newLock creates a new synchronization lock based on Go channels.
func newLock() chan int {
	ch := make(chan int, 1)
	ch <- 0 // lock starts out unlocked

	return ch
}

// tryLock attempts to get access to a lock. Attempt is tried
// LOCK_NUM_RETRIES waiting LOCK_WAIT milliseconds between each
// attempt. Returns a boolean indicating whether access was
// acquired or not.
func tryLock(lock <-chan int) bool {
	for i := 0; i < LOCK_NUM_RETRIES; i++ {
		select {
		case <-lock:
			return true

		default:
			time.Sleep(time.Duration(LOCK_WAIT) * time.Millisecond)
		}
	}

	return false
}

// releaseLock releases a previously acquired lock (with
// tryLock). Panics if the lock is not currently locked.
func releaseLock(lock chan<- int) {
	select {
	case lock <- 0:
		return
	default:
		// fmt.Printf("Warning: Attempt to release unlocked lock\n")
		// panic("Attempt to release unlocked lock")
	}
}

// An indicator for whether some archetype resource operations are able to block.
// Some resources do not allow blocking once acquired, so such a resource should
// indicate this by setting the bit.
// All resources should have a non-blocking path (where they spuriously fail if they
// cannot make progress, rather than blocking indefinitely), and must take it if
// the bit is set. If not, they may block indefinitely, such that behaviour will be
// indistinguishable from a critical section that has not yet begun executing.
type RiskBit *bool

// ArchetypeResource defines the interface that parameters passed to functions
// derived from Modular PlusCal's archetypes must implement.
type ArchetypeResource interface {
	// Acquire attempts to get access to a resource with read and/or write
	// permissions. Returns a boolean indicating whether it was successful.
	Acquire(access ResourceAccess, riskBit RiskBit) error

	// Read returns the current value associated with a resource.
	// Resource needs to have been acquired first.
	Read(riskBit RiskBit) (interface{}, error)

	// Write receives a new value that the underlying resource is
	// supposed to be set to.
	Write(value interface{}, riskBit RiskBit) error

	// Release causes the calling process to cease having access to the
	// shared resource. Any written changes to the underlying values
	// are committed.
	Release() error

	// Abort indicates an error situation. Access must be released,
	// and any state changed while the resource was accquired is
	// rolled back to its previous value, before acquisition
	Abort() error

	// Less compares one archetype resource with another. Since
	// archetype resources are ordered based on priority, Less() is
	// only invoked to determine how to order two different resources
	// of the same priority. For that reason it is safe to cast
	// the `other` argument to the concrete implementation of this
	// interface when implementing Less.
	Less(other ArchetypeResource) bool
}

// ArchetypeResourceCollection represents archetype resources that are
// mapped via function calls in Modular PlusCal. Instead of using
// regular indexing operations, the Get allows implementations to
// provide custom archetype resources that depend on the value being
// indexed.
type ArchetypeResourceCollection interface {
	// Get receives as input the value being indexed on, and returns
	// the corresponding archetype resource. Note that different
	// implementations have specific requirements for the type of
	// `value`.
	//
	// Note that the resource returned by Get() must either be
	// stateless *or* Get() must return the same resource when called
	// with the same `value` argument
	Get(value interface{}) ArchetypeResource
}

// SortableArchetypeResource represents a collection of archetype
// resources.  This type implements the functions necessary to enable
// a collection of archetype resources to be sorted using Go's
// `sort.Sort` utility.
type SortableArchetypeResource []ArchetypeResource

func (s SortableArchetypeResource) Len() int {
	return len(s)
}

// Sorting occurs in-place.
func (s SortableArchetypeResource) Swap(i, j int) {
	s[i], s[j] = s[j], s[i]
}

func (s SortableArchetypeResource) Less(i, j int) bool {
	// if the resource was not registered, panic
	typeI := reflect.TypeOf(s[i]).Elem()
	if _, exists := priorityMap[typeI]; !exists {
		panic(fmt.Sprintf("Resource type not registered: %T", s[i]))
	}

	typeJ := reflect.TypeOf(s[j]).Elem()
	if _, exists := priorityMap[typeJ]; !exists {
		panic(fmt.Sprintf("Resource type not registered: %T", s[j]))
	}

	prioI := priorityMap[typeI]
	prioJ := priorityMap[typeJ]

	// if the priorities are different, return the one with lowest
	// priority
	if prioI != prioJ {
		return prioI < prioJ
	}

	// same priority: do type-specific comparison
	return s[i].Less(s[j])
}

// AcquireResources acquires a series of resources (concrete
// implementations of the `ArchetypeResource` interface) and returns
// an error in case one of the resources cannot be acquired. This
// function makes sure that resources are acquired in proper order
// (i.e., according to the resource's implementation of `Less`).
func AcquireResources(access ResourceAccess, riskBit RiskBit, resources ...ArchetypeResource) error {
	// sort the resources to be acquired according to their
	// implementation of `Less`
	sort.Sort(SortableArchetypeResource(resources))
	numAcquired := 0

	// resources are now ordered
	for _, r := range resources {
		err := r.Acquire(access, riskBit)

		// if there is an error acquiring one of the resources, abort access
		// to all of the previously acquired resources and return the error
		if err != nil {
			for i := 0; i < numAcquired; i++ {
				resources[i].Abort()
			}

			return err
		}

		numAcquired++
	}

	return nil
}

// ReleaseResources releases a collection of archetype resources
// simultaneously. If the values associated with these archetypes were
// updated (via Write calls on the archetypes), this will make the
// changes visible (committed). It makes sure that resources are
// released according to the order defined by the resource's
// implementation of `Less`.
func ReleaseResources(resources ...ArchetypeResource) error {
	sort.Sort(SortableArchetypeResource(resources))
	numAcquired := 0
	var err error

	for _, r := range resources {
		err = r.Release()

		// if there is an error releasing one of the resources, abort all
		// subsequent resources and return the error
		if err != nil {
			for i := numAcquired; i < len(resources); i++ {
				resources[i].Abort()
			}
		}

		numAcquired++
	}

	return err
}

// AbortResources releases (without modification) a collection of
// archetype resources simulaneously. It makes sure that resources are
// released according to the order defined by the resource's
// implementation of `Less`.
func AbortResources(resources ...ArchetypeResource) error {
	sort.Sort(SortableArchetypeResource(resources))

	for _, r := range resources {
		if err := r.Abort(); err != nil {
			return err
		}
	}

	return nil
}

////////////////////////////////////////////////
////         ARCHETYPE RESOURCES            ////
////////////////////////////////////////////////

// Global State as Archetype Resource
// ----------------------------------

// Global variable is one type of archetype resource. It is backed by the
// StateServer implementation in this package.
type GlobalVariable struct {
	name         string
	stateServer  *StateServer
	refs         VarReferences
	writtenValue interface{}
}

// Variable is a convenience function to create a GlobalVariable struct from
// a previously configured StateServer. The returned GlobalVariable can be
// passed to archetypes, and the state represented by this variable will be
// managed by all peers in the system.
func (ss *StateServer) Variable(name string) *GlobalVariable {
	return &GlobalVariable{
		name:         name,
		stateServer:  ss,
		refs:         nil,
		writtenValue: nil,
	}
}

// Acquire wraps the underlying StateServer struct, creating a proper BorrowSpec
// and attempting to borrow the value from this node's peers in the network.
func (v *GlobalVariable) Acquire(access ResourceAccess, riskBit RiskBit) error {
	if v.refs != nil {
		return &ResourceInternalError{fmt.Sprintf("variable %s already acquired", v.name)}
	}
	// riskBit is true if a global variable is used, due to mutex-like behaviour
	*riskBit = true

	var spec BorrowSpec

	if access&READ_ACCESS != 0 {
		spec.ReadNames = []string{v.name}
	}

	if access&WRITE_ACCESS != 0 {
		spec.WriteNames = []string{v.name}
	}

	refs, err := v.stateServer.Acquire(&spec)
	if err != nil {
		return &ResourceInternalError{err.Error()}
	}

	v.refs = refs
	return nil
}

// Read returns the value associated with a global variable. It *must*
// have been acquired before.
func (v *GlobalVariable) Read(_ RiskBit) (interface{}, error) {
	return v.refs.Get(v.name), nil
}

// Write updates previously obtained references (via `Acquire`) to
// the value passed to this function.
func (v *GlobalVariable) Write(value interface{}, _ RiskBit) error {
	v.writtenValue = value
	return nil
}

// Release makes changes made while the variable was acquired visible
// to other processes.
func (v *GlobalVariable) Release() error {
	if v.writtenValue != nil {
		v.refs.Set(v.name, v.writtenValue)
	}

	err := v.stateServer.Release(v.refs)
	v.refs = nil

	if err != nil {
		return &ResourceInternalError{err.Error()}
	}

	return nil
}

// Abort releases access (previously obtained via `Acquire`) without modifying
// the underlying value of a variable.
func (v *GlobalVariable) Abort() error {
	err := v.stateServer.Release(v.refs)
	v.refs = nil

	if err != nil {
		return &ResourceInternalError{err.Error()}
	}

	return nil
}

// Less implements ordering between global variables by performing
// lexicographical sorting over their names.
func (v *GlobalVariable) Less(other ArchetypeResource) bool {
	gv := other.(*GlobalVariable)
	return strings.Compare(v.name, gv.name) < 0
}

// Mailboxes as Archetype Resource
// -------------------------------

// Receiver represents the interface exposed by mailboxes. When data
// is received by a process, the data is sent across the underlying Go
// channel and can be read on calls to 'Read'.
type Receiver struct {
	ch chan interface{}
}

// Receive receives data from the other end of the channel.
func (r *Receiver) Receive(val *interface{}, result *int) error {
	select {
	case r.ch <- *val:
		*result = RPC_SUCCESS
	default:
		*result = MAILBOX_IS_FULL_ERROR
	}

	return nil
}

func mailboxErrorDescription(e int) string {
	if e == MAILBOX_IS_FULL_ERROR {
		return "Destination mailbox is full"
	} else {
		return fmt.Sprintf("Unknown mailbox error code: %d", e)
	}
}

// Mailbox is an implementation of `ArchetypeResource` that provides
// an abstraction of a queue of messages that are waiting to be
// processed by some process. Other processes compiled by PGo are able
// to communicate with the running process by means of sending
// messages (Write() calls); processes may then read the next message
// available in their queues.
type Mailbox struct {
	name           string            // internal name exposed via RPC
	version        int               // version of this service being created
	selfNames      []string          // identifiers deployed at the node that created the mailbox
	configuration  map[string]string // configuration of the system (PlusCal process -> IP address)
	conns          *Connections      // the set of connections to nodes within the system
	readAttempts   int               // number of times to attempt a read when no message is buffered
	waitDuration   int               // how long to wait between two read attempts (in ms)
	readBuf        []interface{}     // messages read from the channel
	writeBuf       []interface{}     // messages waiting to be sent when the channel is released
	readChan       chan interface{}  // reads are buffered through Go channels
	timeout        uint              // how long to wait for RPC calls
	readingAborted bool              // whether we are reading messages from a previously aborted transaction
	lock           sync.Mutex        // exclusive access to internal buffers
}

// service returns the name of the RPC service associated with this
// mailbox.
func (mbox *Mailbox) service() string {
	return "Mailbox_" + mbox.name + "_" + strconv.Itoa(mbox.version)
}

func (mbox *Mailbox) callAsync(function string, args interface{}, ok *int) *rpc.Call {
	fName := mbox.service() + "." + function
	addr := mbox.configuration[mbox.name]
	return mbox.conns.GetConnection(addr).Go(fName, &args, ok, nil)
}

func (mbox *Mailbox) sendMessage(msg interface{}) error {
	var result int
	call := mbox.callAsync("Receive", msg, &result)

	checkRPCResult := func() error {
		if result != RPC_SUCCESS {
			return fmt.Errorf("Mailbox communication error: %s", mailboxErrorDescription(result))
		}

		return nil
	}

	// a timeout of 0 indicates that the system TCP timeout should be
	// used
	if mbox.timeout == 0 {
		<-call.Done
		if call.Error != nil {
			return call.Error
		}

		return checkRPCResult()
	}

	// send the message asynchronously; if it times out, return an
	// error
	select {
	case <-call.Done:
		if call.Error != nil {
			return call.Error
		}

		return checkRPCResult()

	case <-time.After(time.Duration(mbox.timeout) * time.Millisecond):
		return fmt.Errorf("Timed out: %v", mbox.service())
	}
}

func tryRead(ch chan interface{}, attempts, wait int, riskBit RiskBit) (interface{}, bool) {
	if *riskBit {
        for i := 0; i < attempts; i++ {
            select {
            case msg := <-ch:
                return msg, true
            default:
                time.Sleep(time.Duration(wait) * time.Millisecond)
            }
        }
    } else {
        // if !*riskBit, we can block indefinitely, because we are outside of any mutex context that could
        // cause liveness issues
        msg := <-ch
        return msg, true
    }

	return nil, false
}

func stringInList(target string, list []string) bool {
	for _, s := range list {
		if target == s {
			return true
		}
	}

	return false
}

// MailboxRef represents a reference to some mailbox. It can be local
// (if the process 'id' is the same as the mailbox being referenced),
// or remote (if they are different).
//
// Processes can send messages to other processes by appending to
// their message queues.
//
// The message queue (mailbox) contains at most 'bufferSize'
// elements. Sending a message to a process with a full queue causes
// the requester to block until sufficient space in the queue is
// available.
//
// The `timeout` argument indicates how long RPC calls should wait for
// the reply of a function call. Passing a timeout of 0 causes the
// runtime to not employ any timeout mechanism (falling back to the
// underlying system's TCP timeout).
func MailboxRef(name string, version int, conns *Connections, configuration map[string]string, ids []string, bufferSize uint, timeout uint) (*Mailbox, error) {
	mbox := &Mailbox{
		name:           name,
		version:        version,
		selfNames:      ids,
		configuration:  configuration,
		conns:          conns,
		readAttempts:   2,
		waitDuration:   20,
		readBuf:        []interface{}{},
		writeBuf:       []interface{}{},
		timeout:        timeout,
		readingAborted: false,
	}

	// if the reference is for the mailbox of the current process,
	// expose RPC calls that allow other processes to send messages to
	// it.
	if stringInList(name, ids) {
		readChan := make(chan interface{}, bufferSize)
		receiver := &Receiver{readChan}
		mbox.readChan = readChan

		if err := conns.ExposeImplementation(mbox.service(), receiver); err != nil {
			return nil, err
		}
	}

	return mbox, nil
}

// Acquire is a no-op for mailboxes
func (_ *Mailbox) Acquire(_ ResourceAccess, _ RiskBit) error {
	return nil
}

// Read attempts to read a message; in cases there are none, it
// returns an AbortRetryError. It is enforced that processes can only
// read messages from their own mailboxes.
func (mbox *Mailbox) Read(riskBit RiskBit) (interface{}, error) {
	if !stringInList(mbox.name, mbox.selfNames) {
		panic(fmt.Sprintf("Tried to read non-local mailbox %s (attempted by %s)", mbox.name, mbox.selfNames))
	}

	mbox.lock.Lock()
	defer mbox.lock.Unlock()

	// if we are still reading messages from an aborted session
	if mbox.readingAborted {
		// read from the buffer of previously read messages (pop from
		// the queue)
		if len(mbox.readBuf) > 0 {
			msg := mbox.readBuf[0]
			mbox.readBuf = mbox.readBuf[1:]
			return msg, nil
		} else {
			// if there are no more previously read messages, we are
			// no longer reading from a previous transaction
			mbox.readingAborted = false
		}
	}

	// if we are not reading from a previous transaction, wait for
	// incoming messages on the mailbox
	var msg interface{}
	var ok bool
	if msg, ok = tryRead(mbox.readChan, mbox.readAttempts, mbox.waitDuration, riskBit); !ok {
		return nil, &AbortRetryError{"No messages in the buffer"}
	}

	mbox.readBuf = append(mbox.readBuf, msg)
	return msg, nil
}

// Write saves a message with the value given in a buffer to be sent
// later, when the channel is released.
func (mbox *Mailbox) Write(value interface{}, _ RiskBit) error {
	mbox.lock.Lock()
	defer mbox.lock.Unlock()

	mbox.writeBuf = append(mbox.writeBuf, value)
	return nil
}

// Release sends each message given to Write() to the destination
// mailbox.
func (mbox *Mailbox) Release() error {
	mbox.lock.Lock()
	defer mbox.lock.Unlock()

	// send each message written to the resource while it was
	// acquired.  Returns an error if sending any message failed
	for _, msg := range mbox.writeBuf {
		if err := mbox.sendMessage(msg); err != nil {
			// return &ResourceInternalError{err.Error()}
			// TODO: this should return a proper ResourceInternalError
			return nil
		}
	}

	// erase read and write buffers
	mbox.readBuf = []interface{}{}
	mbox.writeBuf = []interface{}{}
	return nil
}

// Abort erases messages passed using Write and returns.  It keeps the
// buffer of read messages so that, when the channel is next acquired,
// the same messages will be read again
func (mbox *Mailbox) Abort() error {
	mbox.lock.Lock()
	defer mbox.lock.Unlock()

	mbox.writeBuf = []interface{}{}
	mbox.readingAborted = true
	return nil
}

// Less implements ordering among mailboxes by doing lexicographical
// sorting over the names of the services exposed over RPC.
func (mbox *Mailbox) Less(other ArchetypeResource) bool {
	otherMBox := other.(*Mailbox)
	return strings.Compare(mbox.service(), otherMBox.service()) < 0
}

// Local Channels as Archetype Resource
// ------------------------------------

// LocalChannelResource represents an archetype resource backed by a
// regular Go channel. The main use-case for channels as resources is
// being able to control the execution of long-running archetypes.
// Parameters can be sent via channels and the result of the
// computation performed can also be transmitted via channels.
type LocalChannelResource struct {
	name         string           // channel identifier
	ch           chan interface{} // the underlying Go channel
	readAttempts int              // how many times to try to read from a channel
	waitDuration int              // how long to wait between each attempt (in ms)
	lock         chan int         // guarantees access to the underlying channel is exclusive
	readBuf      []interface{}    // keeps track of read values
	writeBuf     []interface{}    // values written to the channel; sent when the resource is released
}

// NewLocalChannel creates a LocalChannelResource. The caller does not
// need to know about the underlying Go channel.
func NewLocalChannel(name string, bufferSize int) *LocalChannelResource {
	return &LocalChannelResource{
		name:         name,
		lock:         newLock(),
		ch:           make(chan interface{}, bufferSize),
		readAttempts: 2,
		waitDuration: 20,
		readBuf:      []interface{}{},
		writeBuf:     []interface{}{},
	}
}

// Acquire tries to get exclusive access to the local channel.
func (localCh *LocalChannelResource) Acquire(access ResourceAccess, _ RiskBit) error {
	if !tryLock(localCh.lock) {
		return &AbortRetryError{"Could not acquire LocalChannelResource"}
	}

	return nil
}

// Read waits for data to be available in the underlying Go channel.
func (localCh *LocalChannelResource) Read(riskBit RiskBit) (interface{}, error) {
	var val interface{}
	var ok bool

	if val, ok = tryRead(localCh.ch, localCh.readAttempts, localCh.waitDuration, riskBit); !ok {
		return nil, &AbortRetryError{"No messages in the channel"}
	}

	localCh.readBuf = append(localCh.readBuf, val)
	return val, nil
}

// Write sends a value over the channel.
func (localCh *LocalChannelResource) Write(value interface{}, _ RiskBit) error {
	localCh.writeBuf = append(localCh.writeBuf, value)
	return nil
}

// Release writes values written to the channel while the resource was
// acquired.
func (localCh *LocalChannelResource) Release() error {
	// send written values over the channel
	for _, val := range localCh.writeBuf {
		localCh.ch <- val
	}

	// erase read and written values
	localCh.readBuf = []interface{}{}
	localCh.writeBuf = []interface{}{}

	// release access to the channel
	releaseLock(localCh.lock)
	return nil
}

// Abort undoes any read performed while the channel was acquired
func (localCh *LocalChannelResource) Abort() error {
	// reverse read values
	for i := len(localCh.readBuf)/2 - 1; i >= 0; i-- {
		opp := len(localCh.readBuf) - 1 - i
		localCh.readBuf[i], localCh.readBuf[opp] = localCh.readBuf[opp], localCh.readBuf[i]
	}

	// send the read values back
	for _, val := range localCh.readBuf {
		localCh.ch <- val
	}

	// erase read and written values
	localCh.readBuf = []interface{}{}
	localCh.writeBuf = []interface{}{}

	// release access to the channel
	releaseLock(localCh.lock)
	return nil
}

// Less implements ordering among instances of
// LocalChannelResource. Lexicographical comparison on their names is
// used.
func (localCh *LocalChannelResource) Less(other ArchetypeResource) bool {
	ch := other.(*LocalChannelResource)
	return strings.Compare(localCh.name, ch.name) < 0
}

// Send writes data to the channel so that the receiving end can see
// it (on a Read call). This is supposed to be called by code outside
// archetypes.
func (localCh *LocalChannelResource) Send(value interface{}) {
	localCh.ch <- value
}

// Receive reads data from the channel so that results can be
// collected. This is supposed to be called by code outside
// archetypes.
func (localCh *LocalChannelResource) Receive() interface{} {
	return <-localCh.ch
}

// Files as Archetype Resource
// ---------------------------

// FileResource implements files in the system as archetype resources.
type FileResource struct {
	path     string   // absolute path to the file
	fd       *os.File // the underlying file descriptor.
	contents []byte   // if the file has been previously read or written, hold contents in buffer
	dirty    bool     // whether the file has been written
}

// NewFileResource creates a FileResource for the file under `path`.
func NewFileResource(path string) *FileResource {
	return &FileResource{
		path:     path,
		contents: nil,
		dirty:    false,
	}
}

// Acquire attempts to open the underlying file with appropriate
// permissions.  Returns an error if it cannot be done.
func (file *FileResource) Acquire(access ResourceAccess, _ RiskBit) error {
	perms := os.O_RDONLY
	if access&WRITE_ACCESS != 0 {
		perms = os.O_RDWR
	}

	fd, err := os.OpenFile(file.path, perms|os.O_CREATE, 0644)
	if err != nil {
		return &ResourceInternalError{err.Error()}
	}

	file.fd = fd
	return nil
}

// Read returns a buffer with all the contents of the underlying file.
// Panics if reading there is a an error reading the file.
func (file *FileResource) Read(_ RiskBit) (interface{}, error) {
	if file.contents == nil {
		data, err := ioutil.ReadAll(file.fd)

		// IO error: let the calller handle it
		if err != nil {
			return nil, &ResourceInternalError{err.Error()}
		}

		file.contents = data
	}

	return file.contents, nil
}

// Write saves the value to be written in an internal
// buffer. Subsequent Read() calls will return the newly written
// value. Note that `value` *must* be []byte.
func (file *FileResource) Write(value interface{}, _ RiskBit) error {
	file.contents = value.([]byte)
	file.dirty = true

	return nil
}

// Release writes any previously written contents to the underlying
// file, and closes it.
func (file *FileResource) Release() error {
	if file.fd != nil {
		if file.dirty {
			_, err := file.fd.Write(file.contents)

			if err != nil {
				return &ResourceInternalError{err.Error()}
			}
		}

		return file.fd.Close()
	}

	return nil
}

// Abort closes the underlying file
func (file *FileResource) Abort() error {
	return file.fd.Close()
}

// Less implements ordering. The file path is used to order instances
// of FileResource.
func (file *FileResource) Less(other ArchetypeResource) bool {
	otherFile := other.(*FileResource)
	return strings.Compare(file.path, otherFile.path) < 0
}

// Immutable Values as Archetype Resources
// ---------------------------------------

type ImmutableResource struct {
	value interface{}
}

// NewImmutableResource creates a new immutable archetype resource
// wrapping the `value` passed.
func NewImmutableResource(value interface{}) *ImmutableResource {
	return &ImmutableResource{value}
}

// Acquire is a no-op for immutable resources
func (_ *ImmutableResource) Acquire(_ ResourceAccess, _ RiskBit) error {
	return nil
}

// Read returns the underlying value
func (resource *ImmutableResource) Read(_ RiskBit) (interface{}, error) {
	return resource.value, nil
}

// Write panics (the resource is immutable)
func (_ *ImmutableResource) Write(value interface{}, _ RiskBit) error {
	panic("Attempted to write immutable resource")
}

// Release is a no-op for immutable resources
func (_ *ImmutableResource) Release() error {
	return nil
}

// Abort is a no-op for immutable resources
func (_ *ImmutableResource) Abort() error {
	return nil
}

// Less is a no-op. Immutable resources are agnostic to ordering.
func (_ *ImmutableResource) Less(_ ArchetypeResource) bool {
	return false
}

// Locally Shared Variables as Archetype Resources
// -----------------------------------------------

// LocallySharedResource represents some value that is shared only locally,
// i.e., within the same Go process.
type LocallySharedResource struct {
	name       string      // resource identifier
	val        interface{} // the value being shared
	writtenBuf interface{} // buffer of previous writes
	lock       chan int    // mutex to guarantee exclusive access
}

// NewLocallySharedResource creates a new shared resource that can be
// used as a resource archetype
func NewLocallySharedResource(name string, val interface{}) *LocallySharedResource {
	return &LocallySharedResource{
		name:       name,
		val:        val,
		writtenBuf: nil,
		lock:       newLock(),
	}
}

// Acquire locks the resource for exclusive access
func (resource *LocallySharedResource) Acquire(_ ResourceAccess, riskBit RiskBit) error {
	*riskBit = true
	if !tryLock(resource.lock) {
		return &AbortRetryError{"Could not acquire LocallySharedResource"}
	}

	return nil
}

// Read returns the current value of the resource
func (resource *LocallySharedResource) Read(_ RiskBit) (interface{}, error) {
	if resource.writtenBuf != nil {
		return resource.writtenBuf, nil
	}

	return resource.val, nil
}

// Write updates the value of the underlying shared resource
func (resource *LocallySharedResource) Write(value interface{}, _ RiskBit) error {
	resource.writtenBuf = value
	return nil
}

// Release writes any written value to the underlying shared value and
// returns
func (resource *LocallySharedResource) Release() error {
	if resource.writtenBuf != nil {
		resource.val = resource.writtenBuf
	}

	releaseLock(resource.lock)
	return nil
}

// Abort erases any values passed using Write and returns.
func (resource *LocallySharedResource) Abort() error {
	resource.writtenBuf = nil
	releaseLock(resource.lock)

	return nil
}

// Less implements ordering among locally shared
// resources. Lexicographical order on the resource name is used.
func (resource *LocallySharedResource) Less(other ArchetypeResource) bool {
	otherResource := other.(*LocallySharedResource)
	return strings.Compare(resource.name, otherResource.name) < 0
}

// AtomicIntegers as Archetype Resources
// -------------------------------------

// AtomicInteger wraps an integer value that can be read from and
// written to without acquiring locks. It makes use of the sync/atomic
// Go package in order to ensure reads and writes are consistent and
// isolated.
type AtomicInteger struct {
	name         string // used to enforce consistent ordering
	value        int32  // the current value of the underlying integer
	writtenValue *int32 // uncommitted write, if any
}

// NewAtomicInteger creates an atomic Integer initialized with the
// value passed as argument
func NewAtomicInteger(name string, initial int32) *AtomicInteger {
	return &AtomicInteger{
		name:  name,
		value: initial,
	}
}

// Acquire is a no-op for atomic integers
func (_ AtomicInteger) Acquire(_ ResourceAccess, _ RiskBit) error {
	return nil
}

// Read returns the current value of the resource
func (aint *AtomicInteger) Read(_ RiskBit) (interface{}, error) {
	if aint.writtenValue != nil {
		return int(*aint.writtenValue), nil
	}

	return int(atomic.LoadInt32(&aint.value)), nil
}

// Write updates the value of the underlying integer
func (aint *AtomicInteger) Write(value interface{}, _ RiskBit) error {
	intValue := int32(value.(int))
	aint.writtenValue = &intValue

	return nil
}

// Release writes any written value to the underlying atomic integer
// and returns.
func (aint *AtomicInteger) Release() error {
	if aint.writtenValue != nil {
		atomic.StoreInt32(&aint.value, *aint.writtenValue)
	}

	return nil
}

// Abort erases any values passed using Write and returns.
func (aint *AtomicInteger) Abort() error {
	aint.writtenValue = nil
	return nil
}

// Less implements ordering among atomic integer resources.
// Lexicographical order on the resource name is used.
func (aint *AtomicInteger) Less(other ArchetypeResource) bool {
	otherResource := other.(*AtomicInteger)
	return strings.Compare(aint.name, otherResource.name) < 0
}

// Sleeping as Archetype Resources
// -------------------------------

// SleepResource allows implementations to sleep an arbitrary duration
// while executing an archetype.
type SleepResource struct {
	name string        // resource name, for ordering
	unit time.Duration // seconds, milliseconds, ...
}

// NewSleepResource creates a resource that sleeps for the specified
// amount of time when the resource is written to. The parameter given
// indicates the unit used when the resource is used (i.e., seconds,
// milliseconds, etc.)
func NewSleepResource(name string, unit time.Duration) *SleepResource {
	return &SleepResource{
		name: name,
		unit: unit,
	}
}

// Acquire is a no-op for sleep resources
func (_ *SleepResource) Acquire(_ ResourceAccess, _ RiskBit) error {
	return nil
}

// Read panics if invoked. Sleep resources should not be read from!
func (_ *SleepResource) Read(_ RiskBit) (interface{}, error) {
	panic("Attempted to read SleepResource")
}

// Write sleeps for the specified amount of time (must be an integer)
func (s *SleepResource) Write(value interface{}, _ RiskBit) error {
	t := value.(int)

	time.Sleep(time.Duration(t) * s.unit)
	return nil
}

// Release is a no-op for sleep resources
func (_ *SleepResource) Release() error {
	return nil
}

// Abort is a no-op for sleep resources
func (_ *SleepResource) Abort() error {
	return nil
}

// Less implements ordering among sleep resources
// Lexicographical order on the resource name is used.
func (s *SleepResource) Less(other ArchetypeResource) bool {
	otherResource := other.(*SleepResource)
	return strings.Compare(s.name, otherResource.name) < 0
}

/////////////////////////////////////////////////////////////////////////
////            ARCHETYPE RESOURCE COLLECTIONS                      ////
///////////////////////////////////////////////////////////////////////

// Slices as Archetype Resource Collections
// ----------------------------------------

// ArchetypeResourceSlice implements implements an
// ArchetypeResourceCollection by mapping Get calls as straightforward
// indexing operations on the underlying slice.
type ArchetypeResourceSlice []ArchetypeResource

// Get returns the archetype resource at a given index. The `value`
// passed must be an integer.
func (slice ArchetypeResourceSlice) Get(value interface{}) ArchetypeResource {
	index := value.(int)
	return slice[index]
}

// File System Directories as Archetype Resource Collections
// ---------------------------------------------------------

// FileSystemDirectory represents an archetype resource that makes the
// files in a certain directory available, implementing the
// ArchetypeResourceCollection interface
type FileSystemDirectory struct {
	root      string                   // path to the directory under which files will be accessed
	resources map[string]*FileResource // maps previously retrieved files
}

// NewFileSystemDirectory returns an implementation of
// ArchetypeResourceCollection for accessing files under a root
// directory.
func NewFileSystemDirectory(root string) *FileSystemDirectory {
	return &FileSystemDirectory{
		root:      root,
		resources: map[string]*FileResource{},
	}
}

// Get returns the archetype resource file corresponding to the path
// (relative to the root) given as argument. The `value` given must be
// a string.
func (dir *FileSystemDirectory) Get(value interface{}) ArchetypeResource {
	relativePath := value.(string)

	if _, ok := dir.resources[relativePath]; !ok {
		absolutePath := path.Join(string(dir.root), relativePath)
		dir.resources[relativePath] = NewFileResource(absolutePath)
	}

	return dir.resources[relativePath]
}

// Singleton collections as Archetype Resource Collection
// ------------------------------------------------------

// SingletonCollectionResource imeplements the
// ArchetypeResourceCollection by trivially always returning the same
// resource for every index.
type SingletonCollectionResource struct {
	resource ArchetypeResource
}

// NewSingletonCollection returns a SingletonCollectionResource
// wrapping the resource given
func NewSingletonCollection(resource ArchetypeResource) SingletonCollectionResource {
	return SingletonCollectionResource{resource}
}

// Get returns the underlying ArchetypeResource.
func (singleton SingletonCollectionResource) Get(_ interface{}) ArchetypeResource {
	return singleton.resource
}

// Maps as Archetype Resource Collections
// --------------------------------------

// ArchetypeResourceMap implements the ArchetypeResourceCollection
// interface and allows Get operations to index on keys of the map.
type ArchetypeResourceMap struct {
	resources map[interface{}]*LocallySharedResource
	counter   uint
	lock      sync.Mutex
}

func NewArchetypeResourceMap() *ArchetypeResourceMap {
	return &ArchetypeResourceMap{
		resources: map[interface{}]*LocallySharedResource{},
	}
}

// Get returns a LocallySharedResource with the value on the given
// `key`.
func (m *ArchetypeResourceMap) Get(key interface{}) ArchetypeResource {
	m.lock.Lock()
	if _, ok := m.resources[key]; !ok {
		// the name is irrelevant here since function-mapped resources
		// are acquired at the time of use
		m.resources[key] = NewLocallySharedResource(fmt.Sprintf("mapResource_%d", m.counter), nil)
	}
	m.counter++

	m.lock.Unlock()
	return m.resources[key]
}

// ToMap returns a Go map representation of the map archetype
// resource.  Any attempts to Get() a value from the map will block
// while this operation is in progress.
func (m *ArchetypeResourceMap) ToMap() map[interface{}]interface{} {
	// make sure the map cannot be changed while we convert the data
	// to a Go map
	m.lock.Lock()

	result := map[interface{}]interface{}{}
	for k, v := range m.resources {
		if v.val != nil {
			result[k] = v.val
		}
	}

	m.lock.Unlock()
	return result
}

// Resource Pools as Archetype Resource Collections
// ------------------------------------------------

// ResourcePool implements a pool of archetype resources that can be
// shared among multiple processes in a system.
type ResourcePool struct {
	size      int                 // the number of resources in the pool
	resources []ArchetypeResource // the actual resources being shared
	free      chan int            // channel containing indices into 'resources' that are free
}

// NewResourcePool creates a resource pool of a given 'size'. The
// 'factory' function is used to create an archetype resource in the
// pool. It is called 'size' types to create the initial pool.
func NewResourcePool(size int, factory func() ArchetypeResource) *ResourcePool {
	pool := &ResourcePool{
		resources: make([]ArchetypeResource, size),
		free:      make(chan int, size),
	}

	// initialize resources and free list
	for i := 0; i < size; i++ {
		pool.resources[i] = factory()
		pool.free <- i
	}

	return pool
}

// Retrieve obtains a free resource in the pool. Blocks until one is
// available if no resources are available at the time of the request.
// Returns a 'handle' that must be returned when the caller is done
// using the resource.
func (pool *ResourcePool) Retrieve() (ArchetypeResource, int) {
	handle := <-pool.free
	return pool.resources[handle], handle
}

// Return marks a previously retrieved resource as free again.
func (pool *ResourcePool) Return(handle int) {
	pool.free <- handle
}

// Get returns the resource associated with the given value
// (handle). It is an error to pass a value that has not been
// previously retrieved.
func (pool *ResourcePool) Get(value interface{}) ArchetypeResource {
	handle := value.(int)
	return pool.resources[handle]
}
