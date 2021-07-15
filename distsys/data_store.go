package distsys

import (
	"bytes"
	"fmt"
	"log"
	"sync"
)

// NameNotFoundError occurs when a lookup for an unknown name in the store is made
type NameNotFoundError string

func (e NameNotFoundError) Error() string {
	return fmt.Sprintf("Local store: name not found: %s", string(e))
}

// DataEntry represents a single piece of global state that is
// contained in this node. Entries are protected by a read-write lock
// in order to make sure that two different nodes trying to read
// from/write to the same piece of global state concurrently will not
// lead to inconsistencies in program execution (race conditions)
type DataEntry struct {
	sync.RWMutex             // protects access this entry
	Value        interface{} // value, which can be of any type
	Owner        string      // address of the node that currently owns this entry
}

// DataStore implements a volatile store that can be used to keep
// track of global state of applications compiled by PGo. State is
// modeled as a table that maps names (such as variable names) to
// values of any type, encapsulated as `DataEntry` structs.
type DataStore map[string]*DataEntry

// NewDataStore creates a new `DataStore` struct. An initial state can
// be given in the `initValues` parameter, which makes sure the state
// local to this node will contain the data passed to this function.
func NewDataStore(initValues map[string]*DataEntry) DataStore {
	return DataStore(initValues)
}

// Lock gives the caller exclusive access to the entry associated with
// the  given `name`.  Blocks if  another thread  currently holds  the
// lock.
func (store DataStore) Lock(name string) {
	store.findOrPanic(name).Lock()
}

// Unlock releases exclusive access previously held by `Lock()`. It is
// an error to call this function without a previous call to Lock().
func (store DataStore) Unlock(name string) {
	store.findOrPanic(name).Unlock()
}

// GetVal returns the value associated with the name in the underlying
// store.  Panics if the name does not exist.
func (store DataStore) GetVal(name string) interface{} {
	return store.findOrPanic(name).Value
}

// SetVal updates the value associated with a given `name` in the
// underlying store.  Invoking this function is only safe if the
// caller has previously called Lock() on the same name. Panics if the
// name does not exist in the store.
func (store DataStore) SetVal(name string, val interface{}) {
	store.findOrPanic(name).Value = val
}

// OwnerOf returns the address of the node that is believed to own the
// given `name`. Panics if the name does not exist.
func (store DataStore) OwnerOf(name string) string {
	return store.findOrPanic(name).Owner
}

// UpdateOwner updates the address of the node that is believed to own
// the `name` given. Invoking this function is only safe if the caller
// has previously called Lock() on the same name. Panics if the name
// does not exist in the store.
func (store DataStore) UpdateOwner(name, owner string) {
	store.findOrPanic(name).Owner = owner
}

func (store DataStore) findOrPanic(name string) *DataEntry {
	entry, inStore := store[name]
	if !inStore {
		log.Panic(NameNotFoundError(name))
	}

	return entry
}

func (data DataStore) String() string {
	var buf bytes.Buffer
	var i int

	for name, entry := range data {
		if i > 0 {
			buf.WriteString(", ")
		}

		buf.WriteString(fmt.Sprintf("%s => %v [%s]", name, entry.Value, entry.Owner))
		i++
	}

	return fmt.Sprintf("Store(%s)", buf.String())
}
