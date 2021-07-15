package distsys

import (
	"math/rand"
	"time"
)

const (
	REF_VAL = iota
	REF_MOVED
	REF_SKIP
)

type MigrationStrategy interface {
	ShouldMigrate(name, requester string) bool
}

type NeverMigrate string

func (never NeverMigrate) ShouldMigrate(_, _ string) bool {
	return false
}

type AlwaysMigrate string

func (always AlwaysMigrate) ShouldMigrate(_, _ string) bool {
	return true
}

type RandomMigrate string

func NewRandomMigrate(self string) RandomMigrate {
	rand.Seed(time.Now().UTC().UnixNano())
	return RandomMigrate(self)
}

func (random RandomMigrate) ShouldMigrate(_, _ string) bool {
	return rand.Float64() > 0.5
}

type RefHandler interface {
	GetRef() *Reference
}

func refBuilder(handler *requestStateHandler, variable *BorrowSpecVariable) RefHandler {
	owner := handler.store.OwnerOf(variable.Name)

	if owner == handler.self {
		if handler.ownershipMiss {
			return RefSkipHandler{variable.Name, handler.store}
		}

		return RefValHandler{
			name:              variable.Name,
			self:              handler.self,
			requester:         handler.requester,
			exclusive:         variable.Exclusive,
			store:             handler.store,
			migrationStrategy: handler.migrationStrategy,
		}
	}

	handler.ownershipMiss = true
	return RefMovedHandler{variable.Name, owner, handler.store}
}

type RefValHandler struct {
	name      string
	self      string
	requester string
	exclusive bool
	store     DataStore

	migrationStrategy MigrationStrategy
}

func (refhandler RefValHandler) GetRef() *Reference {
	var peer string
	val := refhandler.store.GetVal(refhandler.name)
	moveOwnership := refhandler.migrationStrategy.ShouldMigrate(refhandler.name, refhandler.requester)

	if moveOwnership {
		// update our ownership table to reflect the migration
		refhandler.store.UpdateOwner(refhandler.name, refhandler.requester)

		// since we are no longer the owners of this variable, free
		// any memory being taken by it
		refhandler.store.SetVal(refhandler.name, nil)
	}

	// indicate the source of the variable ownership so that an
	// ACK can be sent back
	peer = refhandler.self

	return &Reference{
		Type: REF_VAL,

		Value:     val,
		Exclusive: refhandler.exclusive,
		Ownership: moveOwnership,
		Peer:      peer,
	}
}

type RefMovedHandler struct {
	name  string
	peer  string
	store DataStore
}

func (refhandler RefMovedHandler) GetRef() *Reference {
	refhandler.store.Unlock(refhandler.name)

	return &Reference{
		Type: REF_MOVED,
		Peer: refhandler.peer,
	}
}

type RefSkipHandler struct {
	name  string
	store DataStore
}

func (refhandler RefSkipHandler) GetRef() *Reference {
	refhandler.store.Unlock(refhandler.name)

	return &Reference{
		Type: REF_SKIP,
	}
}

// localStateHandler is responsible for manipulating requests for global state that is
// to be present in this node's local store.
type localStateHandler struct {
	group *VarReq   // the variables to be manipulated, including their permissions
	store DataStore // the underlying data store
	self  string    // address of the running node
}

// GetState returns a list of REF_VAL references for the variables contained
// in the VarReq struct within the localStateHandler (receiver). This function
// can only be safely called if the caller holds the lock for all variables
// involved.
func (handler localStateHandler) GetState() (VarReferences, error) {
	refs := VarReferences(map[string]*Reference{})

	for _, borrowVar := range handler.group.Names {
		handler := RefValHandler{
			name:      borrowVar.Name,
			exclusive: borrowVar.Exclusive,
			self:      handler.self,
			store:     handler.store,

			// no migrations since this is a local request
			migrationStrategy: NeverMigrate(handler.self),
		}

		refs.insert(borrowVar.Name, handler.GetRef())
	}

	return refs, nil
}

// ReleaseState updates the underlying data store with potentially updated
// values in the VarReferences struct given.
func (handler localStateHandler) ReleaseState(refs VarReferences) error {
	for name, ref := range refs {
		if ref.Exclusive {
			handler.store.SetVal(name, ref.Value)
		}
	}

	return nil
}

type requestStateHandler struct {
	group         *VarReq   // the variables to be manipulated, including their permissions
	requester     string    // the address of the node making the request
	store         DataStore // the underlying data store
	self          string    // address of the running node
	ownershipMiss bool      // whether some variable in `group` is not owned by this node

	migrationStrategy MigrationStrategy
}

func (handler requestStateHandler) GetState() (VarReferences, error) {
	refs := VarReferences(map[string]*Reference{})

	for _, borrowVar := range handler.group.Names {
		handler.store.Lock(borrowVar.Name)

		ref := refBuilder(&handler, borrowVar).GetRef()
		refs.insert(borrowVar.Name, ref)
	}

	return refs, nil
}

func (handler requestStateHandler) ReleaseState(refs VarReferences) error {
	for name, ref := range refs {
		if ref.Exclusive {
			handler.store.SetVal(name, ref.Value)
		}

		handler.store.Unlock(name)
	}

	return nil
}

// StateMoveComplete is called when a name's ownership is sent to another node
// in the system, and the receiving node acknowledges that it has updates its
// local store to reflect the fact that it now owns that state.
func (handler requestStateHandler) StateMoveComplete() {
	for _, borrowVar := range handler.group.Names {
		handler.store.Unlock(borrowVar.Name)
	}
}
