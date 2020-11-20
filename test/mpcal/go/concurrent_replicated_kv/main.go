package main

import (
	"bufio"
	"fmt"
	"io"
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
	MAILBOX_SIZE      = 1000 // message buffer size
	CLOCK_UPDATE_TICK = 80   // clock update 0.2s

	CLIENT_POOL_SIZE   = 100
	CONNECTION_TIMEOUT = 1000 // time out RPC calls after 1s

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
var mboxPool *distsys.ResourcePool
var replicas distsys.ArchetypeResourceCollection

var clientId distsys.ArchetypeResource
var clock distsys.ArchetypeResourceCollection
var lock sync.Mutex

// replica variables
var db *distsys.ArchetypeResourceMap

// storage check mutex
var mut sync.Mutex

// continue ticking?
var tick bool

// change to run every command in a separate Go routine
var concurrentMode = true

type Command interface {
	Run() chan bool
}

type Get struct {
	key string
}

func runCommand(cmd func()) {
	if concurrentMode {
		go cmd()
		return
	}

	cmd()
}

func (g Get) Run() chan bool {
	done := make(chan bool, 1)

	runCommand(func() {
		resource, handle := mboxPool.Retrieve()
		defer mboxPool.Return(handle)

		mailbox := distsys.NewSingletonCollection(resource)
		mboxAddress := (self-replicated_kv.NUM_REPLICAS)*CLIENT_POOL_SIZE + handle

		getKey := distsys.NewImmutableResource(g.key)
		response := distsys.NewLocallySharedResource("getResponse", nil)

		if err := replicated_kv.Get(mboxAddress, clientId, replicas, mailbox, getKey, clock, spin, response); err != nil {
			panic(fmt.Sprintf("Get error: %v", err))
		}

		// Read without Acquire because we know `response` is not
		// shared
		response.Read(new(bool))
		done <- true
	})

	return done
}

type Put struct {
	key   string
	value string
}

func (p Put) Run() chan bool {
	done := make(chan bool, 1)
	runCommand(func() {
		resource, handle := mboxPool.Retrieve()
		defer mboxPool.Return(handle)

		mailbox := distsys.NewSingletonCollection(resource)
		mboxAddress := (self-replicated_kv.NUM_REPLICAS)*CLIENT_POOL_SIZE + handle

		putKey := distsys.NewImmutableResource(p.key)
		putValue := distsys.NewImmutableResource(p.value)
		response := distsys.NewLocallySharedResource("putResponse", nil)

		if err := replicated_kv.Put(mboxAddress, clientId, replicas, mailbox, putKey, putValue, clock, spin, response); err != nil {
			panic(fmt.Sprintf("Put error: %v", err))
		}

		done <- true
	})

	return done
}

type Disconnect int

func (d Disconnect) Run() chan bool {
	done := make(chan bool, 1)
	runCommand(func() {
		disconnect()
		done <- true
	})

	return done
}

func init() {
	if len(os.Args) < 2 {
		fmt.Printf("Usage: %s processName(processArgument)\n", os.Args[0])
	}

	id = os.Args[1]
	configuration = map[string]string{
		"Replica(0)": "127.0.0.1:5555",
		"Replica(1)": "127.0.0.1:6666",
		"Client(2)":  "127.0.0.1:2222",
		"Client(3)":  "127.0.0.1:3333",
		"Client(4)":  "127.0.0.1:4444",
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
	tick = true
}

func fatal(msg string) {
	fmt.Fprintf(os.Stderr, fmt.Sprintf("%s\n", msg))
	os.Exit(1)
}

func makeMailboxRef(name string, version int) *distsys.Mailbox {
	mbox, err := distsys.MailboxRef(name, version, connections, configuration, []string{id}, MAILBOX_SIZE, CONNECTION_TIMEOUT)
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
	return replicated_kv.Disconnect(self, clientId, replicas, clock)
}

func clockUpdate() error {
	for tick {
		time.Sleep(CLOCK_UPDATE_TICK * time.Millisecond)

		if err := replicated_kv.ClockUpdate(self, clientId, replicas, clock, spin); err != nil {
			panic(fmt.Sprintf("Clock Update error: %v\n", err))
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

	fmt.Printf("Replica snapshot (%d keys):\n", len(storage))
	keys := []string{}

	for k, _ := range storage {
		keys = append(keys, k.(string))
	}

	sort.Strings(keys)
	for _, k := range keys {
		fmt.Printf("\t%s -> %s\n", k, storage[k].(string))
	}
}

func main() {
	// if role == "Replica" {
	// 	f, err := ioutil.TempFile("/tmp", "replica.prof")
	// 	if err != nil {
	// 		fatal(err.Error())
	// 	}

	//	pprof.StartCPUProfile(f)
	// 	defer func() {
	// 		pprof.StopCPUProfile()
	// 		fmt.Printf("CPU profile saved at: %s\n", f.Name())
	// 	}()
	// }

	var commands []Command

	// parse commands immediately to avoid finding out invalid command
	// after all processes are up
	if role == "Client" {
		reader := bufio.NewReader(os.Stdin)
		defs := []string{}
		for {
			line, err := reader.ReadString('\n')
			if err == io.EOF {
				break
			} else if err != nil {
				fatal(fmt.Sprintf("IO Error: %v", err))
			}

			defs = append(defs, line)
		}

		commands = parseCommands(defs)
	}

	// set up connections
	clientConns := []distsys.ArchetypeResource{}
	replicaConns := []distsys.ArchetypeResource{}

	for _, i := range replicated_kv.ReplicaSet() {
		replicaConns = append(replicaConns, makeMailboxRef(fmt.Sprintf("Replica(%d)", i), 0))
		clientConns = append(clientConns, nil)
	}

	replicas = distsys.ArchetypeResourceSlice(replicaConns)

	resources := []distsys.ArchetypeResource{}
	for _, clientId := range replicated_kv.ClientSet() {
		for i := 0; i < CLIENT_POOL_SIZE; i++ {
			resources = append(resources, makeMailboxRef(fmt.Sprintf("Client(%d)", clientId), i))
		}
	}
	clients = distsys.ArchetypeResourceSlice(resources)

	// create the mailbox resource pool if we are a client
	if role == "Client" {
		j := (self - replicated_kv.NUM_REPLICAS) * CLIENT_POOL_SIZE
		mboxPool = distsys.NewResourcePool(CLIENT_POOL_SIZE, func() distsys.ArchetypeResource {
			r := resources[j]
			j++

			return r
		})
	}

	// wait for all process to come online
	waitBarrier()

	if role == "Client" {
		clientId = distsys.NewImmutableResource(self)
		clock = distsys.NewSingletonCollection(distsys.NewAtomicInteger("clock", 0))

		initClientRoutines()

		ch := []chan bool{}
		for _, command := range commands {
			ch = append(ch, command.Run())
		}

		// wait for all commands to complete
		for _, c := range ch {
			<-c
		}

		// once all commands are finished, disconnect
		disconnect()

	} else if role == "Replica" {
		db = distsys.NewArchetypeResourceMap()
		go replicated_kv.AReplica(self, clients, replicas, db)
	}

	// wait for all clients to disconnect
	waitBarrier()

	if role == "Replica" {
		// print the storage status if it hasn't been print before
		mut.Lock()
		dumpStorage()
	}
}
