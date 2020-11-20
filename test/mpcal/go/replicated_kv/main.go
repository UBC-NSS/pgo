package main

import (
	"fmt"
	"os"
	"replicated_kv"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"pgo/distsys"
)

const (
	MAILBOX_SIZE      = 10  // message buffer size
	CLOCK_UPDATE_TICK = 200 // clock update 0.2s

	CONNECTION_TIMEOUT = 1000 // time out RPC calls after 1s

	REPLICA_STATUS_CHECK = 5 // print replica database state every 5 seconds

	GET = iota
	PUT
	DISCONNECT
)

var configuration map[string]string
var id string
var role string
var selfStr string
var self int
var connections *distsys.Connections
var barrier *distsys.SyncBarrier
var err error

var spin distsys.ArchetypeResource

// connections to clients and replicas
var clients distsys.ArchetypeResourceCollection
var replicas distsys.ArchetypeResourceCollection

var clientId distsys.ArchetypeResource
var clock distsys.ArchetypeResourceCollection
var locked distsys.ArchetypeResourceCollection

// replica variables
var db *distsys.ArchetypeResourceMap

// storage check mutex
var mut sync.Mutex
var checkCount int

// continue ticking?
var tick bool

type Command interface {
	Run() error
}

type Get struct {
	key string
}

func (g Get) Run() error {
	getKey := distsys.NewImmutableResource(g.key)
	response := distsys.NewLocallySharedResource("getResponse", nil)

	replicated_kv.Get(self, clientId, replicas, clients, getKey, locked, clock, spin, response)

	// Read without Acquire because we know `response` is not
	// shared
	val, _ := response.Read(new(bool))
	if val == nil {
		fmt.Printf("-- Get %s: %v\n", g.key, nil)
	} else {
		fmt.Printf("-- Get %s: %s\n", g.key, val.(string))
	}

	return nil
}

type Put struct {
	key   string
	value string
}

func (p Put) Run() error {
	putKey := distsys.NewImmutableResource(p.key)
	putValue := distsys.NewImmutableResource(p.value)
	response := distsys.NewLocallySharedResource("putResponse", nil)

	replicated_kv.Put(self, clientId, replicas, clients, putKey, putValue, locked, clock, spin, response)

	fmt.Printf("-- Put (%s, %s): OK\n", p.key, p.value)
	return nil
}

type Disconnect int

func (d Disconnect) Run() error {
	return disconnect()
}

func init() {
	if len(os.Args) < 2 {
		fmt.Printf("Usage: %s processName(processArgument)\n", os.Args[0])
	}

	id = os.Args[1]
	configuration = map[string]string{
		"Replica(0)": "127.0.0.1:4444",
		"Replica(1)": "127.0.0.1:5555",
		"Replica(2)": "127.0.0.1:6666",
		"Client(3)":  "127.0.0.1:2222",
		"Client(4)":  "127.0.0.1:3333",
	}

	if _, ok := configuration[id]; !ok {
		fmt.Fprintf(os.Stderr, "Unknown process: %s\n", id)
		os.Exit(1)
	}

	ipPort := configuration[id]
	role, selfStr = distsys.ParseProcessId(id)
	coordinator := configuration["Replica(1)"]
	connections = distsys.NewConnections(ipPort)
	barrier = distsys.NewSyncBarrier(configuration, connections, ipPort, coordinator)

	self, err = strconv.Atoi(selfStr)
	if err != nil {
		panic(err)
	}

	// archetype resource functions do not spin in this context
	spin = distsys.NewImmutableResource(false)

	checkCount = 0
	tick = true
}

func fatal(msg string) {
	fmt.Fprintf(os.Stderr, fmt.Sprintf("%s\n", msg))
	os.Exit(1)
}

func makeMailboxRef(name string) *distsys.Mailbox {
	mbox, err := distsys.MailboxRef(name, 0, connections, configuration, []string{id}, MAILBOX_SIZE, CONNECTION_TIMEOUT)
	if err != nil {
		panic(err)
	}

	return mbox
}

func waitBarrier() {
	if err := barrier.WaitPeers(); err != nil {
		fatal(fmt.Sprintf("Error: %v\n", err))
	}
}

func parseCommands(defs []string) []Command {
	if len(defs) == 0 {
		fatal("Clients need at least one command")
	}

	commands := []Command{}

	for _, c := range defs {
		fields := strings.Fields(c)

		action := strings.ToUpper(fields[0])
		if action == "GET" {
			if len(fields) != 2 {
				fatal(fmt.Sprintf("Invalid command: %s", c))
			}

			key := fields[1]
			commands = append(commands, Get{key: key})

		} else if action == "PUT" {
			if len(fields) != 3 {
				fatal(fmt.Sprintf("Invalid command: %s", c))
			}

			key := fields[1]
			val := fields[2]

			commands = append(commands, Put{key: key, value: val})

		} else if action == "DISCONNECT" {
			if len(fields) != 1 {
				fatal(fmt.Sprintf("Invalid command: %s", c))
			}

			commands = append(commands, Disconnect(0))

		} else {
			fatal(fmt.Sprintf("Invalid command: %s", c))
		}
	}

	return commands
}

func disconnect() error {
	return replicated_kv.Disconnect(self, clientId, replicas, locked, clock)
}

func clockUpdate() error {
	for tick {
		time.Sleep(CLOCK_UPDATE_TICK * time.Millisecond)

		if err := replicated_kv.ClockUpdate(self, clientId, replicas, clock, spin); err != nil {
			fmt.Printf("Clock Update error: %v\n", err)
			return err
		}
	}

	return nil
}

func initClientRoutines() {
	// set up ClockUpdate routine
	go clockUpdate()
}

func dumpStorage() {
	storage := db.ToMap()

	if len(storage) == 0 {
		fmt.Printf("Replica snapshot: (empty)\n")
		return
	}

	fmt.Printf("Replica snapshot:\n")
	keys := []string{}

	for k, _ := range storage {
		keys = append(keys, k.(string))
	}

	sort.Strings(keys)
	for _, k := range keys {
		fmt.Printf("\t%s -> %s\n", k, storage[k].(string))
	}
}

func storageStatusCheck() {
	for {
		time.Sleep(REPLICA_STATUS_CHECK * time.Second)
		mut.Lock()

		dumpStorage()
		checkCount += 1

		mut.Unlock()
	}

}

func main() {
	var commands []Command

	// parse  command line options  soon to avoid finding  out invalid
	// command after all processes are up
	if role == "Client" {
		commands = parseCommands(os.Args[2:])
	}

	// set up connections
	clientConns := []distsys.ArchetypeResource{}
	replicaConns := []distsys.ArchetypeResource{}

	for _, i := range replicated_kv.ReplicaSet() {
		replicaConns = append(replicaConns, makeMailboxRef(fmt.Sprintf("Replica(%d)", i)))
		clientConns = append(clientConns, nil)
	}

	for _, i := range replicated_kv.ClientSet() {
		clientConns = append(clientConns, makeMailboxRef(fmt.Sprintf("Client(%d)", i)))
	}

	clients = distsys.ArchetypeResourceSlice(clientConns)
	replicas = distsys.ArchetypeResourceSlice(replicaConns)

	// wait for all process to come online
	waitBarrier()

	if role == "Client" {
		if len(os.Args) == 3 {
			fmt.Fprintf(os.Stderr, "Client requires a list of commands")
			os.Exit(1)
		}

		clientId = distsys.NewImmutableResource(self)
		locked = distsys.NewSingletonCollection(distsys.NewLocallySharedResource("locked", false))
		clock = distsys.NewSingletonCollection(distsys.NewLocallySharedResource("clock", 0))

		initClientRoutines()

		for _, command := range commands {
			command.Run()
		}

	} else if role == "Replica" {
		db = distsys.NewArchetypeResourceMap()
		go replicated_kv.AReplica(self, clients, replicas, db)
		go storageStatusCheck()
	}

	// wait for all clients to disconnect
	waitBarrier()

	// all process are done, stop ticking the clock
	tick = false

	if role == "Replica" {
		// print the storage status if it hasn't been print before
		mut.Lock()

		if checkCount == 0 {
			dumpStorage()
		}
	}
}
