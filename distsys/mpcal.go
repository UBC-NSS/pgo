package distsys

import (
	"errors"
	"fmt"
)

var AssertionFailed = errors.New("assertion failed")

// What is definition of this struct?
type ArchetypeResourceHandle struct {
	Tag   int
	Index int
	Name  string
}

const (
	ArchetypeResourceNamedTag = iota
	ArchetypeResourceIndexedTag
)

type MPCalDurableStorageRecord struct {
	Resources       []ArchetypeResource
	Frame           int
	FrameStack      []int
	ResourcesByName map[string]ArchetypeResource
	CommitPending   map[ArchetypeResourceHandle]bool
}

func (record *MPCalDurableStorageRecord) getResourceByHandle(handle ArchetypeResourceHandle) ArchetypeResource {
	switch handle.Tag {
	case ArchetypeResourceNamedTag:
		return record.ResourcesByName[handle.Name]
	case ArchetypeResourceIndexedTag:
		return record.Resources[handle.Index]
	default:
		panic(fmt.Errorf("could not find archetype resource by handle %v", handle))
	}
}

type MPCalDurableStorage interface {
	RecoverResources() (rec *MPCalDurableStorageRecord, err error)
	SnapshotResources(rec *MPCalDurableStorageRecord)
}

// I suggest writing definition of important types like this exactly. In this case, it's not trivial
// to see that MPCalContext closely resembles logic of critical section and it can be confusing.
// Moreover, I suggest defining MPCalContext as an interface.
type MPCalContext struct {
	durableStorage MPCalDurableStorage
	record         MPCalDurableStorageRecord
}

func NewMPCalContext(durableStorage MPCalDurableStorage) (*MPCalContext, error) {
	record, err := durableStorage.RecoverResources()
	if err != nil {
		return nil, err
	}
	if record == nil {
		record = &MPCalDurableStorageRecord{
			ResourcesByName: make(map[string]ArchetypeResource),
		}
	}
	if record.CommitPending != nil {
		var nonTrivialOutstandingCommits []chan struct{}
		for resHandle := range record.CommitPending {
			ch := record.getResourceByHandle(resHandle).Commit()
			if ch != nil {
				nonTrivialOutstandingCommits = append(nonTrivialOutstandingCommits, ch)
			}
		}
		for _, ch := range nonTrivialOutstandingCommits {
			<-ch
		}
		for resHandle := range record.CommitPending {
			delete(record.CommitPending, resHandle)
		}
		durableStorage.SnapshotResources(record)
	}
	return &MPCalContext{
		durableStorage: durableStorage,
		record:         *record,
	}, nil
}

type MPCalContextArchetypeConfigFn func(durability MPCalDurableStorage, resource ArchetypeResource)

// What does ensurer do exactly?
type MPCalContextResourceEnsurer func(blank ArchetypeResource, configFn func(resource ArchetypeResource)) ArchetypeResourceHandle

func (ctx *MPCalContext) ResourceEnsurerByName(name string) MPCalContextResourceEnsurer {
	return func(blank ArchetypeResource, configFn func(ArchetypeResource)) ArchetypeResourceHandle {
		resource, ok := ctx.record.ResourcesByName[name]
		if !ok {
			ctx.record.ResourcesByName[name] = blank
			resource = blank
		}
		configFn(resource)
		return ArchetypeResourceHandle{
			Tag:  ArchetypeResourceNamedTag,
			Name: name,
		}
	}
}

func (ctx *MPCalContext) ResourceEnsurerPositional() MPCalContextResourceEnsurer {
	return func(blank ArchetypeResource, configFn func(ArchetypeResource)) ArchetypeResourceHandle {
		var resource ArchetypeResource
		if ctx.record.Frame == len(ctx.record.Resources) {
			resource = blank
			ctx.record.Resources = append(ctx.record.Resources, blank)
		} else {
			resource = ctx.record.Resources[ctx.record.Frame]
		}
		configFn(resource)
		resourcePosition := ctx.record.Frame
		ctx.record.Frame += 1
		return ArchetypeResourceHandle{
			Tag:   ArchetypeResourceIndexedTag,
			Index: resourcePosition,
		}
	}
}

func (ctx *MPCalContext) PositionalResourceStackPush() {
	ctx.record.FrameStack = append(ctx.record.FrameStack, ctx.record.Frame)
}

func (ctx *MPCalContext) PositionalResourceStackPop() {
	ctx.record.Frame = ctx.record.FrameStack[len(ctx.record.FrameStack)-1]
	ctx.record.FrameStack = ctx.record.FrameStack[:len(ctx.record.FrameStack)-1]
	ctx.record.Resources = ctx.record.Resources[:ctx.record.Frame]
}

func (ctx *MPCalContext) Abort() {
	if ctx.record.CommitPending == nil {
		return
	}
	var nonTrivialAborts []chan struct{}
	for resHandle := range ctx.record.CommitPending {
		ch := ctx.record.getResourceByHandle(resHandle).Abort()
		if ch != nil {
			nonTrivialAborts = append(nonTrivialAborts, ch)
		}
	}
	for _, ch := range nonTrivialAborts {
		<-ch
	}

	// clear any touched resources (compiler will optimise this, see https://golang.org/doc/go1.11#performance-compiler)
	for resHandle := range ctx.record.CommitPending {
		delete(ctx.record.CommitPending, resHandle)
	}
}

func (ctx *MPCalContext) Commit() (err error) {
	if ctx.record.CommitPending == nil {
		return // in the unlikely event this is reachable, skip it
	}

	// dispatch all parts of the pre-commit phase asynchronously, so we only wait as long as the slowest resource
	var nonTrivialPreCommits []chan error
	for resHandle := range ctx.record.CommitPending {
		ch := ctx.record.getResourceByHandle(resHandle).PreCommit()
		if ch != nil {
			nonTrivialPreCommits = append(nonTrivialPreCommits, ch)
		}
	}
	for _, ch := range nonTrivialPreCommits {
		localErr := <-ch
		if localErr != nil {
			err = localErr
		}
	}

	// if there was an error, stop now, and expect either (1) total crash of (2) Abort to be called
	if err != nil {
		return
	}

	// we commit to committing, so apply any durable persistence here, so we recover to this point if we crash
	ctx.durableStorage.SnapshotResources(&ctx.record)

	// same as above, run all the commit processes async
	var nonTrivialCommits []chan struct{}
	for resHandle := range ctx.record.CommitPending {
		ch := ctx.record.getResourceByHandle(resHandle).Commit()
		if ch != nil {
			nonTrivialCommits = append(nonTrivialCommits, ch)
		}
	}
	for _, ch := range nonTrivialCommits {
		<-ch
	}

	// if we have not crashed, we successfully committed everything, so snapshot state again, but without
	// the in-progress commit, as we are done.
	for resHandle := range ctx.record.CommitPending {
		delete(ctx.record.CommitPending, resHandle)
	}
	ctx.durableStorage.SnapshotResources(&ctx.record)
	return
}

func (ctx *MPCalContext) ensureCriticalSectionWith(handle ArchetypeResourceHandle) {
	if ctx.record.CommitPending == nil {
		ctx.record.CommitPending = make(map[ArchetypeResourceHandle]bool)
	}
	ctx.record.CommitPending[handle] = true
}

func (ctx *MPCalContext) Write(handle ArchetypeResourceHandle, indices []TLAValue, value TLAValue) (err error) {
	ctx.ensureCriticalSectionWith(handle)
	res := ctx.record.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	err = res.WriteValue(value)
	return
}

func (ctx *MPCalContext) Read(handle ArchetypeResourceHandle, indices []TLAValue) (value TLAValue, err error) {
	ctx.ensureCriticalSectionWith(handle)
	res := ctx.record.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	value, err = res.ReadValue()
	return
}
