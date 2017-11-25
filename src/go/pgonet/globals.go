package pgonet

// Implements the global state management API.
//
// Currently, PGo manages global state in a distributed environment by using the
// `etcd' key-value store. The functions defined here wrap that behaviour by providing
// a get/set interface so that if ever the way that we store global variables change,
// our API (and the code generated by the compiler) may hopefully stay the same.
//
// Usage:
//
// 	import (
// 		"fmt"
// 		"pgonet"
// 	)
//
// 	config := &GlobalsConfig{
// 		Endpoints: []string{"10.0.0.1:1234", "10.0.0.2:1234"},
// 		Timeout: 3,
// 	}
// 	state, err := pgonet.InitGlobals(config)
// 	if err != nil {
// 		// handle error
// 	}
//
// 	err = state.Set("project", "PGo")
// 	if err != nil {
// 		// handle error
// 	}
//
// 	val, err := state.GetString("project")
// 	if err != nil {
// 		// handle error
// 	}
// 	fmt.Printf("project value has value: %s\n", val) // project has value: PGo
//
// 	// Integers are also supported
// 	err = state.Set("count", 42)
// 	if err != nil {
// 		// handle error
// 	}
// 	count, err := state.Get("count")
// 	if err != nil {
// 		// handle error
// 	}
// 	fmt.Printf("count has value: %d\n", count) // count has value: 42

// Implementation Details
//
// Global variables are stored in `etcd' as name => JSON object pairs. The JSON object
// that represents a variable contains information about the variable's current value,
// as well as its type (only ints and strings are currently supported).
//
// This representation is internal and applications need not know about it.

import (
	"context"
	"encoding/json"
	"strconv"
	"time"

	etcd "github.com/coreos/etcd/client"
)

type GlobalVariableType int

// declares the types of global variables supported by PGoNet at the moment.
const (
	PGONET_TYPE_INT = iota
	PGONET_TYPE_STRING
)

// Specifies how to connect to our global state management
type GlobalsConfig struct {
	Endpoints []string // a list of etcd endpoints in the IP:PORT format
	Timeout   int      // the timeout for each operation
}

// A reference to our global state, created via +InitGlobals+. Used in the
// generated Go code to set and get the values of global variables.
type GlobalState struct {
	c  etcd.Client
	kv etcd.KeysAPI
}

// a global variable, as stored in the key-value store
type globalVariable struct {
	Value string
	Type  GlobalVariableType
}

// Initializes centralized global state management.
//
// The only currently supported global state management is the `centralized'
// strategy - that is, every request to global state is sent to the same server
// (or collection of servers).
//
// Returns a reference to `pgonet.GlobalState' on success. Fails if we cannot
// establish a connection to the etcd cluster.
func InitGlobals(cfg *GlobalsConfig) (*GlobalState, error) {
	etcdConfig := etcd.Config{
		Endpoints:               cfg.Endpoints,
		HeaderTimeoutPerRequest: cfg.Timeout * time.Second,
	}

	c, err := etcd.New(etcdConfig)
	if err != nil {
		return nil, err
	}

	return &GlobalState{
		c:  c,
		kv: etcd.NewKeysAPI(c),
	}, nil
}

// Sets variable `name' to a given `value'. Contacts the global variable server
// *synchronously*
func (self *GlobalState) Set(name string, value interface{}) error {
	switch val := value.(type) {
	case int:
		return setInt(name, val)
	case string:
		return setString(name, val)
	default:
		return fmt.Errorf("Unsupported global variable type: %T\n", value)
	}
}

// Gets the value associated with a variable with the given `name'. The variable value
// is cast to an int and returned (the method fails if the value exists and is not a
// valid int). Contacts the global variable server *synchronously*
func (self *GlobalState) GetInt(name string) (int, error) {
	response, err := self.kv.Get(context.Background(), prepareKey(name), nil)
	if err != nil {
		return "", err
	}

	intVal, err := strconv.Atoi(response.Node.Value)
	if err != nil {
		return "", err
	}

	return intVal, nil
}

func (self *GlobalState) GetString(name string) (string, error) {
	response, err := self.kv.Get(context.Background(), prepareKey(name), nil)
	if err != nil {
		return "", err
	}

	return response.Node.Value, nil
}

func (self *GlobalState) setInt(name string, value int) error {
	variable := globalVariable{
		Value: strconv.Itoa(value),
		Type:  PGONET_TYPE_INT,
	}

	_, err := self.kv.Set(context.Background(), prepareKey(name), serialize(variable), nil)
	return err
}

func (self *GlobalState) setString(name, value string) error {
	variable := globalVariable{
		Value: value,
		Type:  PGONET_TYPE_STRING,
	}

	_, err := self.kv.Set(context.Background(), prepareKey(name), serialize(variable), nil)
	return err
}

// given a key k, this method transforms it to the format expected by `etcd'
func prepareKey(k string) string {
	return "/" + k
}

func serialize(v globalVariable) string {
	b, _ := json.Marshal(v)
	return string(b)
}

func parse(s string) globalVariable {
	var v globalVariable
	json.Unmarshal(s, &v)

	return v
}
