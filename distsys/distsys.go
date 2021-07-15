package distsys

import (
	"github.com/mitchellh/hashstructure/v2"

	"bytes"
	"encoding/gob"
	"fmt"
	"log"
	"sort"
	"strings"
)

// UnknownOwnerError happens when a lookup for a certain piece of global
// state on the ownership table does not yield any result
type UnknownOwnerError struct {
	name string
}

func (e *UnknownOwnerError) Error() string {
	return fmt.Sprintf("Ownership table lookup failed: no owner for variable %s", e.name)
}

// BorrowSpec specifies a borrow request from a node to another. It includes a list
// of variables names for which exclusive access is required, as well as a list of
// names for which non-exclusive access is sufficient
type BorrowSpec struct {
	ReadNames  []string // which variables we are reading (non-exclusive access)
	WriteNames []string // which variables we are writing (exclusive access)
}

// BorrowSpecVariable represents a the borrowing requirements of a single variable
// within a `BorrowSpec`
type BorrowSpecVariable struct {
	Name      string
	Exclusive bool
}

func (specv *BorrowSpecVariable) String() string {
	var exclusive string
	if specv.Exclusive {
		exclusive = " [exclusive]"
	}

	return fmt.Sprintf("BorrowSpecVariable(%s%s)", specv.Name, exclusive)
}

type SortedBorrowSpec []*BorrowSpecVariable

func (sbs SortedBorrowSpec) String() string {
	var buf bytes.Buffer
	var i int

	for _, specv := range sbs {
		if i > 0 {
			buf.WriteString(", ")
		}

		buf.WriteString(fmt.Sprintf("%v", specv))
		i++
	}

	return fmt.Sprintf("[%s]", buf.String())
}

func (spec SortedBorrowSpec) Len() int {
	return len(spec)
}

func (spec SortedBorrowSpec) Swap(i, j int) {
	spec[i], spec[j] = spec[j], spec[i]
}

func (spec SortedBorrowSpec) Less(i, j int) bool {
	return strings.Compare(spec[i].Name, spec[j].Name) < 0
}

// Sorted returns a list of requested names in the borrow spec in alphabetical order.
func (spec *BorrowSpec) Sorted() SortedBorrowSpec {
	// remove duplicates across read and write names
	namesSet := map[string]bool{}

	for _, readVar := range spec.ReadNames {
		namesSet[readVar] = true
	}

	for _, writeVar := range spec.WriteNames {
		namesSet[writeVar] = true
	}

	names := []*BorrowSpecVariable{}
	for name, _ := range namesSet {
		writeVariable := false

		// if the current variable is a write-variable, access to
		// it must be declared exclusive
		for _, writeVar := range spec.WriteNames {
			if writeVar == name {
				writeVariable = true
				break
			}
		}

		names = append(names, &BorrowSpecVariable{
			Name:      name,
			Exclusive: writeVariable,
		})
	}

	sort.Sort(SortedBorrowSpec(names))
	return SortedBorrowSpec(names)
}

func (spec *BorrowSpec) String() string {
	return fmt.Sprintf("BorrowSpec[ReadNames=(%s) | WriteNames=(%s)]",
		strings.Join(spec.ReadNames, ","), strings.Join(spec.WriteNames, ","))
}

// Reference represents a variable reference. It indicates the current variable
// value and whether the reference is exclusive (no other node has access to
// it, and allows the node to mutate the value).
type Reference struct {
	Type int // the type of reference: REF_VAL or REF_MOVED

	// Used when Type == REF_VAL
	Value     interface{} // the value of a variable reference
	Exclusive bool        // whether access to this value is exclusive
	Ownership bool        // whether the ownership of the state is being moved with the reference

	// Used when Type == REF_MOVED
	Peer string
}

func (ref Reference) String() string {
	var owns, exclusive, typeDesc string
	if ref.Ownership {
		owns = " [owns]"
	}

	if ref.Exclusive {
		exclusive = "*"
	}

	if ref.Type == REF_VAL {
		typeDesc = "VAL"
	} else if ref.Type == REF_MOVED {
		typeDesc = fmt.Sprintf("MOVED:%s", ref.Peer)
	} else {
		typeDesc = "SKIP"
	}

	return fmt.Sprintf("Ref(%v%s%s (%s))", ref.Value, exclusive, owns, typeDesc)
}

// VarReferences maps variable names to references. Can be used when a node is
// transferring state it knows about to another node in the system
type VarReferences map[string]*Reference

// insert populates a VarReferences struct with a (potentially new) name
func (self VarReferences) insert(name string, ref *Reference) {
	self[name] = ref
}

// Set is used by clients when updating global state locally (once ownership of
// the global state has been acquired). Panics if the name given does not
// exist in the VarReferences struct (a situtation that could only happen if
// the developer makes changes to the generated source code)
func (self VarReferences) Set(name string, val interface{}) {
	ref, found := self[name]
	if !found {
		log.Panicf("Attempt to set unknown variable: %s", name)
	}

	ref.Value = val
}

// Get is used by clients reading global state locally (once the running node
// has successfully borrowed or owns the given name). Panics if the name given
// does not exist in the VarReferences struct.
func (self VarReferences) Get(name string) interface{} {
	if _, found := self[name]; !found {
		log.Panicf("Attempt to get unknown variable: %s", name)
	}

	return self[name].Value
}

// Merge takes another VarReferences object and merges it with the receiver.
// Returns a new VarReferences struct that includes references from both objects
func (self VarReferences) Merge(other VarReferences) VarReferences {
	// optimization: if the VarReferences passed as argument to this function
	// does not contain any reference, just return the target unmodified
	if len(other) == 0 {
		return self
	}

	newrefs := map[string]*Reference{}

	for name, ref := range self {
		newrefs[name] = ref
	}

	for name, ref := range other {
		newrefs[name] = ref
	}

	return VarReferences(newrefs)
}

// ToBorrowSpec transforms a VarReferences struct into a corresponding BorrowSpec
// struct. The BorrowSpec struct returned contains the same names as the original
// VarReferences, with the same exclusive access rights. However, the translation
// is lossy -- values stored in VarReferences are not present in BorrowSpec.
func (self VarReferences) ToBorrowSpec() *BorrowSpec {
	spec := BorrowSpec{
		ReadNames:  []string{},
		WriteNames: []string{},
	}

	for name, ref := range self {
		if ref.Exclusive {
			spec.WriteNames = append(spec.WriteNames, name)
		} else {
			spec.ReadNames = append(spec.ReadNames, name)
		}
	}

	sort.Strings(spec.ReadNames)
	sort.Strings(spec.WriteNames)
	return &spec
}

func (self VarReferences) String() string {
	var buf bytes.Buffer
	var i int

	for name, ref := range self {
		if i > 0 {
			buf.WriteString(", ")
		}

		buf.WriteString(fmt.Sprintf("%s => %v", name, ref))
		i++
	}

	return fmt.Sprintf("VarReferences(%s)", buf.String())
}

// GlobalStateOperation represents an attempt to get access to a set of variables
// from the system's global state. Depending on which variables are requested and
// who owns each part of it, this struct is able to group variables together
// in order to minimize the number of requests necessary to get access to the
// state requested
type GlobalStateOperation struct {
	spec        *BorrowSpec
	store       DataStore
	self        string
	connections *Connections

	ownerships     []string
	ackMigrationTo string
}

// NewGlobalStateOperation returns a new instance of GlobalStateOperation for
// the borrow specification passed as argument.
func NewGlobalStateOperation(spec *BorrowSpec, store DataStore, self string, connections *Connections) *GlobalStateOperation {
	readNames := make([]string, len(spec.ReadNames))
	writeNames := make([]string, len(spec.WriteNames))

	// create an internal copy of the borrow spec being used since it is modified internally
	// on calls to `UpdateRefs`
	copy(readNames, spec.ReadNames)
	copy(writeNames, spec.WriteNames)
	specCopy := &BorrowSpec{
		ReadNames:  readNames,
		WriteNames: writeNames,
	}

	return &GlobalStateOperation{
		spec:        specCopy,
		store:       store,
		self:        self,
		connections: connections,

		ownerships: []string{},
	}
}

// Lock acquires exclusive access to all variables contained in the
// BorrowSpec
func (global *GlobalStateOperation) Lock() {
	for _, borrowVar := range global.spec.Sorted() {
		global.store.Lock(borrowVar.Name)
	}
}

// Unlock releases exclusive access, previously held with Lock(), to
// the variables in this BorrowSpec
func (global *GlobalStateOperation) Unlock() {
	for _, borrowVar := range global.spec.Sorted() {
		global.store.Unlock(borrowVar.Name)
	}
}

// UnlockExcept unlocks every variable in the BorrowSpec of the receiver
// except for the ones contained in the VarReq struct given as
// parameters. This is used when the caller wants to process a group
// of variables (owned by the same node) at a time.
func (global *GlobalStateOperation) UnlockExcept(req *VarReq) {
	for _, borrowVar := range global.spec.Sorted() {
		// if variable is in the group, skip
		skip := false
		for _, reqVar := range req.Names {
			if reqVar.Name == borrowVar.Name {
				skip = true
				break
			}
		}

		if skip {
			continue
		}

		// if variable is not in the group, unlock it
		global.store.Unlock(borrowVar.Name)
	}
}

// HasNext returns true when there are more variables to be processed
// (i.e., get a `REF_VALUE`) in the BorrowSpec passed on initialization
func (global *GlobalStateOperation) HasNext() bool {
	return len(global.spec.ReadNames) > 0 || len(global.spec.WriteNames) > 0
}

// Next returns the next group of variables to be processed by
// the caller. Should be used before a call to `Next` is made.
func (global *GlobalStateOperation) Next() *VarReq {
	return global.Groups()[0]
}

// UpdateRefs updates the global state operation with a set of references
// obtained either from the local state handler, or from a remote node
// in the system.
func (global *GlobalStateOperation) UpdateRefs(refs VarReferences) VarReferences {
	holds := VarReferences(map[string]*Reference{})

	// Updating references for a new group -- clean any previously held
	// data about past ownership moves.
	global.ownerships = []string{}
	global.ackMigrationTo = ""

	for name, ref := range refs {
		switch ref.Type {
		case REF_VAL:
			if ref.Peer != global.self {
				global.store.Lock(name)
			}

			holds[name] = ref

			// if the ownership of this piece of state was transmitted with the
			// reference itself, update our state accordingly
			if ref.Ownership {
				global.owns(name, ref)
			}

			global.deleteFromSpec(name)

		case REF_MOVED:
			// update ownership table
			global.store.UpdateOwner(name, ref.Peer)

		case REF_SKIP:
			// skip
		}
	}

	return holds
}

// updates internal data structures when the reference given includes ownership
// of the state it contains
func (global *GlobalStateOperation) owns(name string, ref *Reference) {
	global.store.UpdateOwner(name, global.self)
	global.store.SetVal(name, ref.Value)

	// collect all ownerships gained
	global.ownerships = append(global.ownerships, name)
	global.ackMigrationTo = ref.Peer
}

func (global *GlobalStateOperation) AckMigrations() {
	if len(global.ownerships) == 0 {
		return
	}

	req := VarReq{Peer: global.self, Names: []*BorrowSpecVariable{}}
	for _, name := range global.ownerships {
		req.Names = append(req.Names, &BorrowSpecVariable{
			Name: name,
		})
	}

	var ok bool
	conn := global.connections.GetConnection(global.ackMigrationTo)

	if err := conn.Call("StateServer.OwnershipMoved", &req, &ok); err != nil {
		log.Panic(err)
	}
}

func (global *GlobalStateOperation) deleteFromSpec(name string) {
	deleted := global.deleteFromCollection(name, &global.spec.ReadNames)
	deleted += global.deleteFromCollection(name, &global.spec.WriteNames)

	if deleted == 0 {
		log.Panicf("Expected to find '%s' in borrow spec, but couldn't", name)
	}
}

// deleteFromCollection looks for the given `name` in the `collection` given,
// and removes it from the slice. Returns the number of elements deleted from
// the collection (i.e., 1 when the name is in the collection, 0 otherwise)
func (global *GlobalStateOperation) deleteFromCollection(name string, collection *[]string) int {
	nameIndex := -1

	for i, rname := range *collection {
		if name == rname {
			nameIndex = i
			break
		}
	}

	if nameIndex == -1 {
		return 0
	}

	(*collection)[nameIndex] = (*collection)[len(*collection)-1]
	*collection = (*collection)[:len(*collection)-1]

	return 1
}

// Groups places the variables contained in a `BorrowSpec` in groupings that minimize
// the number of network calls necessary to get access to the global state required.
// Given the state of the ownership table at the time of call, this function will
// group variables based on ownership.
//
// Examples:
//   ownershipTable := NewOwnershipTable(map[string]string{
//     "a": "10.10.10.1",
//     "b": "10.10.10.1",
//     "c": "10.10.10.3",
//   })
//
//   borrowSpec := BorrowSpec{
//     ReadNames:  []string{"a", "b", "c"},
//     WriteNames: []string{"b"},
//   }
//
//   op := GlobalStateOperation(spec: &spec, ownership: ownershipTable)
//   op.Groups() // =>
//     []*VarReq{
//       *VarReq{Peer: "10.10.10.1", Names: []*BorrowSpecVariable{{Name: "a", Exclusive: false}, ... },
//       *VarReq{Peer: "10.10.10.3", Names: []*BorrowSpecVariable{{Name: "c", Exclusive: false}, ...}
//     }
func (global *GlobalStateOperation) Groups() []*VarReq {
	reqs := []*VarReq{}
	sorted := global.spec.Sorted()

	// if borrow spec is empty, return early
	if len(sorted) == 0 {
		return reqs
	}

	var currentPeer string
	var currVarReq *VarReq
	for _, borrowVar := range sorted {
		owner := global.store.OwnerOf(borrowVar.Name)

		// if this is the first iteration, the current peer is the owner
		// of the current variable
		if len(currentPeer) == 0 {
			currentPeer = owner
			currVarReq = &VarReq{
				Peer:  currentPeer,
				Names: []*BorrowSpecVariable{},
			}
		}

		if owner == currentPeer {
			currVarReq.Names = append(currVarReq.Names, borrowVar)
		} else {
			reqs = append(reqs, currVarReq)

			currentPeer = owner
			currVarReq = &VarReq{
				Peer:  currentPeer,
				Names: []*BorrowSpecVariable{borrowVar},
			}
		}
	}

	// add last group to the list of requests
	reqs = append(reqs, currVarReq)

	return reqs
}

// VarReq represents a request to be sent to another peer in the system. It encapsulates
// the address of the peer as well as the pieces of state required from it
type VarReq struct {
	Peer      string                // the node to which this request should be sent
	Requester string                // the node sending the request
	Names     []*BorrowSpecVariable // maps state names to whether exclusive access is required or not
}

func (req *VarReq) String() string {
	return fmt.Sprintf("VarReq(Peer=%s, Names=%s)", req.Peer, SortedBorrowSpec(req.Names).String())
}

// StateServer represents the current state of the global state at a given time, including
// all the information the running node currently stores, as well as ownership information
// for all pieces of global state
type StateServer struct {
	*SyncBarrier

	self          string            // the address of the running node
	configuration map[string]string // a map from processes to addresses of all peers in the system
	store         DataStore         // the underlying state store

	migrationStrategy MigrationStrategy // determines when to migrate data from a node to another
}

// StateServerRPC wraps the StateServer struct so that only a few methods are
// exposed as RPC methods to other peers in the network
type StateServerRPC struct {
	server *StateServer
}

// NewStateServer creates a new instance of the StateServer struct and sets up algorithm start
// across all peers in the system. This function can only be invoked once the addresses of all
// nodes in the system is known, as well as the initial values for every piece of global state
// in the system. This function will block until all other nodes in the system are also started
// and invoke their corresponding NewStateServer function on their ends.
func NewStateServer(configuration map[string]string, address, coordinator string, initValues map[string]interface{}, migration MigrationStrategy) (*StateServer, error) {
	barrier := NewSyncBarrier(configuration, NewConnections(address), address, coordinator)

	foundAddress := false
	foundCoordinator := false
	for _, addr := range configuration {
		if addr == address {
			foundAddress = true
		}

		if addr == coordinator {
			foundCoordinator = true
		}
	}
	// Make sure `address` and `coordinator` are in the list of peers
	if !foundAddress {
		panic("given address is not in system configuration")
	}
	if !foundCoordinator {
		panic("coodinator is not in system configuration")
	}

	entries := map[string]*DataEntry{}

	// at first, all state is owned by the coordinator node
	for name, _ := range initValues {
		var val interface{}
		if barrier.isCoordinator() {
			val = initValues[name]
		}

		entries[name] = &DataEntry{Value: val, Owner: coordinator}
	}

	stateServer := &StateServer{
		SyncBarrier: barrier,

		self:          address,
		configuration: configuration,
		store:         NewDataStore(entries),

		migrationStrategy: migration,
	}

	if err := stateServer.connections.ExposeImplementation("StateServer", &StateServerRPC{stateServer}); err != nil {
		return nil, err
	}

	return stateServer, nil
}

// DefineCustomType allows the appplication to use user-defined types
// (e.g., Go structs) when communicating with other processes compiled
// by PGo.
func DefineCustomType(value interface{}) {
	gob.Register(value)
}

// Hash returns a uint64 representation for arbitrary data types.
func Hash(value interface{}) uint64 {
	result, err := hashstructure.Hash(value, hashstructure.FormatV2, nil)
	if err != nil {
		panic(fmt.Sprintf("Cannot hash value: %v", value))
	}

	return result
}
