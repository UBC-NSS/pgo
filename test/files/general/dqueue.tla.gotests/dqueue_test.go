package dqueue

import (
	"github.com/UBC-NSS/pgo/distsys"
	"testing"
)

func TestNUM_NODES(t *testing.T) {
	result := NUM_NODES(Constants{NUM_CONSUMERS: distsys.NewTLANumber(12)})
	if result.AsNumber() != 13 {
		t.Errorf("NUM_CONSUMERS should have yielded 13, got %v", result)
	}
}

type dummyDurableStorage struct{}

var _ distsys.MPCalDurableStorage = &dummyDurableStorage{}

func (d dummyDurableStorage) RecoverResources() (rec *distsys.MPCalDurableStorageRecord, err error) {
	return nil, nil
}

func (d dummyDurableStorage) SnapshotResources(rec *distsys.MPCalDurableStorageRecord) {
	// pass
}

func TestProducerConsumer(t *testing.T) {
	producerCtx, err := distsys.NewMPCalContext(&dummyDurableStorage{})
	if err != nil {
		panic(err)
	}
	producerSelf := distsys.NewTLANumber(1)
	producerInputChannel := make(chan distsys.TLAValue, 3)

	consumerCtx, err := distsys.NewMPCalContext(&dummyDurableStorage{})
	if err != nil {
		panic(err)
	}
	consumerSelf := distsys.NewTLANumber(2)
	consumerOutputChannel := make(chan distsys.TLAValue, 3)

	constants := Constants{
		PRODUCER: producerSelf,
	}

	go func() {
		network := distsys.EnsureTCPMailboxesArchetypeResource(producerCtx.ResourceEnsurerByName("network"), func(index distsys.TLAValue) (distsys.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 1:
				return distsys.TCPMailboxesLocal, "localhost:8001"
			case 2:
				return distsys.TCPMailboxesRemote, "localhost:8002"
			default:
				panic("TODO")
			}
		})
		s := distsys.EnsureInputChannelResource(producerCtx.ResourceEnsurerByName("s"), producerInputChannel)
		err := AProducer(producerCtx, producerSelf, constants, network, s)
		if err != nil {
			panic(err)
		}
	}()

	go func() {
		network := distsys.EnsureTCPMailboxesArchetypeResource(consumerCtx.ResourceEnsurerByName("network"), func(index distsys.TLAValue) (distsys.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 1:
				return distsys.TCPMailboxesRemote, "localhost:8001"
			case 2:
				return distsys.TCPMailboxesLocal, "localhost:8002"
			default:
				panic("TODO")
			}
		})
		proc := distsys.EnsureOutputChannelResource(consumerCtx.ResourceEnsurerByName("proc"), consumerOutputChannel)
		err := AConsumer(consumerCtx, consumerSelf, constants, network, proc)
		if err != nil {
			panic(err)
		}
	}()

	producedValues := []distsys.TLAValue{
		distsys.NewTLAString("foo"),
		distsys.NewTLAString("bar"),
		distsys.NewTLAString("ping"),
	}
	for _, value := range producedValues {
		producerInputChannel <- value
	}

	consumedValues := []distsys.TLAValue{<-consumerOutputChannel, <-consumerOutputChannel, <-consumerOutputChannel}
	close(consumerOutputChannel)

	if len(consumedValues) != len(producedValues) || !consumedValues[0].Equal(producedValues[0]) || !consumedValues[1].Equal(producedValues[1]) || !consumedValues[2].Equal(producedValues[2]) {
		t.Errorf("Consumed values %v did not match produced values %v", consumedValues, producedValues)
	}
}
