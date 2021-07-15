package distsys

// This implements a unified way to connect to other proceses and expose an implementation
// that other processes can call.
//
// It uses Go's RPC library under the hood. Extensions to this abstraction could involve
// the definition of a interface that could be implemented by multiple communication methods
// (i.e., not only RPC but other types of protocols, if needed).

import (
	"fmt"
	"net"
	"net/rpc"
	"sync"
)

// Connections maintain the state of the connections across the processes in the network.
type Connections struct {
	address  string                 // the IP:port combination that identifies the current process
	listener *net.TCPListener       // where the server is listening to, if at all
	server   *rpc.Server            // RPC server instance, if this process exposes methods to the network
	network  map[string]*rpc.Client // existing connections to other processes
	lock     sync.Mutex             // exclusive access to the metadata
}

// NewConnections returns an empty connection map.
func NewConnections(addr string) *Connections {
	return &Connections{
		address: addr,
		server:  nil,
		network: map[string]*rpc.Client{},
	}
}

// binds to the address given on initialization. Does nothing if this method was
// already invoked before
func (c *Connections) prepareRPCServer() error {
	// server already exists, nothing to do here
	if c.server != nil {
		return nil
	}

	// bind to this process's address
	tcpaddr, err := net.ResolveTCPAddr("tcp", c.address)
	if err != nil {
		return err
	}

	listener, err := net.ListenTCP("tcp", tcpaddr)
	if err != nil {
		return err
	}

	c.listener = listener
	c.server = rpc.NewServer()
	go c.server.Accept(listener)

	return nil
}

// ExposeImplementation associates a name with an implementation
// Other processes may then connect to this node and invoke the
// exposed methods under the name given.
func (c *Connections) ExposeImplementation(name string, impl interface{}) error {
	if err := c.prepareRPCServer(); err != nil {
		return err
	}

	return c.server.RegisterName(name, impl)
}

// ConnectTo builds a TCP connection to a given node in the address given.
func (c *Connections) ConnectTo(addr string) error {
	c.lock.Lock()
	defer c.lock.Unlock()

	// if the connection already exists, nothing to do here
	if _, connected := c.network[addr]; connected {
		return nil
	}

	client, err := rpc.Dial("tcp", addr)
	if err != nil {
		return err
	}

	c.network[addr] = client
	return nil
}

// GetConnection returns a connection to the node with the given address. If a
// connection to that node already exists, it is returned; otherwise, a new
// connection is established.
func (c *Connections) GetConnection(addr string) *rpc.Client {
	conn, ok := c.network[addr]
	if ok {
		return conn
	}

	// an error here should only occur if the initialization protocol was not
	// used. To properly handle failures, this connection management implementation
	// could be specialized to deal with scenarios where the node is not reachable
	if err := c.ConnectTo(addr); err != nil {
		panic(fmt.Sprintf("Node at %s is not ready to receive connections (error: %v)", addr, err))
	}

	return c.network[addr]
}

// Close terminates all connections to other nodes and stops accepting remote
// connections from other peers.
func (c *Connections) Close() {
	if c.listener != nil {
		c.listener.Close()
	}

	for _, conn := range c.network {
		conn.Close()
	}
}
