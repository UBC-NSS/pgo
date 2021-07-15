----------------------------- MODULE replicated_kv -----------------------------
(***************************************************************************************)
(* Specifies a simple replicated Key-Value store in MPCal.                             *)
(*                                                                                     *)
(* Specifies a replicated state machines (RSM) approach as described in:               *)
(*                                                                                     *)
(* Implementing fault-tolerant services using the state machine approach: a tutorial.  *)
(* http://dl.acm.org/citation.cfm?id=98167                                             *)
(***************************************************************************************)

\* Use some built-in TLA+ modules
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Constant Definitions
\* --------------------

\* Defines the size of the network buffer in a FIFOChannel (the mapping macro).
\*
\* TLC will explore states with up to `BUFFER_SIZE` messages being held on the buffer.
\* If the communication buffer is full, a process that attempts to send a message will not
\* run until a message on the other end of the channel is received.
CONSTANT BUFFER_SIZE

\* Defines the number of key-value store replicas and clients in the system. The specification
\* is orthogonal to these numbers. Note, however, that increasing the number of replicas and/or
\* clients exponentially increases the state space that TLC needs to explore in order to model
\* check your specification.
CONSTANTS NUM_REPLICAS, NUM_CLIENTS

\* When a client sends a message to a replica, the client needs to be able to identify
\* what type of message it just received. These constants below are such labels. Make sure
\* to give them distinct concrete values when model checking.
CONSTANTS DISCONNECT_MSG, GET_MSG, PUT_MSG, NULL_MSG

\* labels that identify a payload corresponds to the response of a previously issues Get
\* or Put request.
CONSTANTS GET_RESPONSE, PUT_RESPONSE

\* an arbitrary `NULL` value. We model the underlying key-value store as a function from
\* a certain key-space (function domain) to this `NULL` element. When a client issues a `PUT`
\* request, the database is updated and the key being set no longer maps to `NULL`.
CONSTANT NULL

\* Defines which keys are used by clients when performing Get and Put operations
\* Since we are interested to test properties like message stability detection
\* and the semantics of the database, we keep these constant throughout model checking.
CONSTANT GET_KEY, PUT_KEY

\* Whenever clients issue PUT requests, they set keys to the value declared in this constant.
CONSTANT PUT_VALUE

\* Defines the set of keys a client may set. In this specification, we restrict
\* it to them to GET_KEY and PUT_KEY
KeySpace == { GET_KEY, PUT_KEY }

\* These constants allow PlusCal processes to derive their client identifiers from
\* their PlusCal identifiers.
GET_ORDER == 0
PUT_ORDER == 1
DISCONNECT_ORDER == 2
NULL_ORDER == 3

\* We have clients that perform each of the operations supported by our Replicated KV-store:
\* Get, Put, Disconnect, and ClockUpdate (or 'null' request). PlusCal requires that every process
\* has a unique identifier. The set definitions below just ensure that our clients have
\* consecutive identifiers.
GetSet == (NUM_REPLICAS)..(NUM_REPLICAS+NUM_CLIENTS-1)
PutSet == (NUM_REPLICAS+NUM_CLIENTS)..(NUM_REPLICAS + 2*NUM_CLIENTS - 1)
DisconnectSet == (NUM_REPLICAS+2*NUM_CLIENTS)..(NUM_REPLICAS+3*NUM_CLIENTS-1)
NullSet == (NUM_REPLICAS+3*NUM_CLIENTS)..(NUM_REPLICAS+4*NUM_CLIENTS-1)

(***************************************************************************
--mpcal ReplicatedKV {
  define {
      \* Define NUM_NODES to be the total number of nodes in the system, i.e., the number of
      \* clients plus the number of replicas
      NUM_NODES == NUM_REPLICAS + NUM_CLIENTS

      \* Each replica and each client in the system need an identifier. By default, replicas
      \* are identified from 1 to NUM_REPLICAS, and the clients are identified from NUM_REPLICAS+1
      \* to NUM_NODES. It is important that identifiers are unique, consecutive and non-overlapping,
      \* due to the way we are modeling our network in this specification.
      ReplicaSet == 0..(NUM_REPLICAS-1)
      ClientSet == NUM_REPLICAS..(NUM_NODES-1)
  }

  \* Broadcasts a certain `msg` to `nodes` with identifiers ranging from
  \* `domainStart` to `domainEnd`.
  \*
  \* Only returns once every message has been sent (i.e., it may "block" if
  \* the buffer of one of the receivers is full).
  macro Broadcast(nodes, i, until, msg, clock) {
      while (i <= until /\ clock # -1) {
          nodes[i] := msg;
          i := i + 1;
      }
  }

  \* Models a FIFO channel. Messages are always delivered. Every process
  \* can have up to `BUFFER_SIZE` messages in its buffer before being
  \* processed.
  mapping macro FIFOChannel {
      read {
          await Len($variable) > 0;
          with (msg = Head($variable)) {
              $variable := Tail($variable);
              yield msg;
          };
      }

      write {
          await Len($variable) < BUFFER_SIZE;
          yield Append($variable, $value);
      }
  }

  \* The following mapping macros make sure that archetypes that
  \* perform client functions read the correct client identifier with
  \* respect to their PlusCal process identifier (`self`).

  mapping macro GetClientId {
      read  { yield self - (NUM_CLIENTS * GET_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  mapping macro PutClientId {
      read  { yield self - (NUM_CLIENTS * PUT_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  mapping macro DisconnectClientId {
      read  { yield self - (NUM_CLIENTS * DISCONNECT_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  mapping macro NullClientId {
      read  { yield self - (NUM_CLIENTS * NULL_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  \* Mapping via identity is sometimes necessary in order to inform
  \* the compiler that a certain resource is to be function mapped, but
  \* no meaningful manipulation on reads and writes is necessary.
  mapping macro Identity {
      read  { yield $variable; }
      write { yield $value; }
  }

  \* This archetype defines the behavior of the replica servers in the system.
  \* Its parameters are:
  \*
  \* - clients: connections to all clients in the system; it needs to wait
  \*            for client requests in order to perform operations.
  \* - replicas: connections to replicas. Since replicas do not talk to each
  \*             other, this parameter is only used in order to listen to
  \*             incoming messages.
  \* - kv: the underlying "database". When 'put' requests become stable, this
  \*       database is updated to include the value being set by the client.
  archetype AReplica(ref clients[_], ref replicas[_], ref kv[_])

  \* Local state in a replica:
  variables
            \* Each replica knows which clients are live (i.e., haven't disconnected)
            \* Initially, all clients are live.
            liveClients = ClientSet,

            \* Replicas remember which requests are pending (i.e., have not been
            \* replied yet). This variable maps client identifiers to a sequence
            \* of pending requests
            pendingRequests = [c \in liveClients |-> <<>>],

            \* Temporary variables: holds messages that are stable
            stableMessages = <<>>,

            \* incremented during in loops
            i,

            \* temporary variable: holds the first pending message from
            \* a client. The first pending message has the lowest logical
            \* clock in the sequence (logical clocks are monotonically increasing)
            firstPending,

            \* temporary variables used while finding the set of stable
            \* messages.
            timestamp,
            nextClient,
            lowestPending,
            chooseMessage,

            \* the replica needs to know the logical clocks of the last
            \* message received by each client in order to determine
            \* request stability.
            currentClocks = [c \in liveClients |-> 0];

            \* determines the lowest logical clock value seen from all
            \* clients. Any pending messages with timestamp lower than this
            \* can be considered stable.
            minClock,

            \* controls while loop execution. See the 'findStableRequestsLoop'
            \* step for more information
            continue,

            \* temporary variable: live clients that have pending
            \* messages (stable or not)
            pendingClients,

            \* Used when iterating over sets of clients
            clientsIter,

            \* used to hold messages sent/received by the replica
            msg,

            \* put requests were successful
            ok,

            \* holds keys/values to be read from/written to the database
            key,
            val; {

    \* Main replica loop. In each iteration of the loop, the replica:
    \*
    \*     1. Waits for incoming messages from clients;
    \*     2. Finds stable messages;
    \*     3. Replies to all stable messages.
    replicaLoop:
      while (TRUE) {

          stableMessages := <<>>;
          continue := TRUE;

          \* Waits for an incoming message from any client. This statement will
          \* "block" the replica until a message is read into 'msg'.
          \* See definition of client archetypes for the format of the messages.
          receiveClientRequest:
            msg := replicas[self];

          \* if the message received is a disconnection from a client,
          \* remove the client from the set of live clients
          clientDisconnected:
            if (msg.op = DISCONNECT_MSG) {
                liveClients := liveClients \ {msg.client};
            };

          \* if the message is a Get request:
          replicaGetRequest:
            if (msg.op = GET_MSG) {
                \* safety assertion: a client requesting for a key must be live
                assert(msg.client \in liveClients);

                \* update our records of the current logical clock of the
                \* requesting client.
                currentClocks[msg.client] := msg.timestamp;

                \* make this a pending message (to be dealt with later, during
                \* stability check)
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            };

          \* if the message is a Put request: similar to Get request.
          replicaPutRequest:
            if (msg.op = PUT_MSG) {
                currentClocks[msg.client] := msg.timestamp;
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            };

          \* if the message is a clock update from a client, inspect the logical clock
          \* to check if it's lower than that of any other message seen before.
          replicaNullRequest:
            if (msg.op = NULL_MSG) {
                currentClocks[msg.client] := msg.timestamp;
            };

          \* Message stability
          \* -----------------
          \*
          \* The replica needs to detect when messages become stable, and then respond to
          \* those messages. Finding out which messages are stable and totally ordering them
          \* is crucial for the correctness of the algorithm. If message stability does not work
          \* correctly in the replicas, the database may get inconsistent across replicas
          \* (if operations are applied in a different order), or clients may get "stuck"
          \* (if stable messages are not replied).


          \* This is the main loop that finds which of the pending requests (if any) are stable
          findStableRequestsLoop:
            while (continue) {

                \* only consider clients that have messages pending
                pendingClients := {c \in liveClients : Len(pendingRequests[c]) > 0};

                \* if two messages have the same logical clock, total ordering is enforced
                \* based on the client identifier: requests from smaller client identifiers
                \* are applied first
                nextClient := NUM_NODES + 1;

                clientsIter := liveClients;
                i := 0;
                minClock := 0;

                \* in order to find the set of stable messages, we need to determine
                \* the lowest logical clock among our set of live clients. Then, every
                \* pending message with a timestamp greater than 'minClock' can be
                \* considered stable.
                findMinClock:
                  while (i < Cardinality(clientsIter)) {
                      with (client \in clientsIter) {
                          if (minClock = 0 \/ currentClocks[client] < minClock) {
                              minClock := currentClocks[client];
                          };

                          clientsIter := clientsIter \ {client};
                      }
                  };

                \* this variable holds the timestamp of the request with the lowest clock
                \* value that is pending and stable
                lowestPending := minClock + 1;

                i := 0;

                \* find the next stable message to be processed
                findMinClient:
                  while (i < Cardinality(pendingClients)) {
                      with (client \in pendingClients) {

                          \* for each client with pending requests:
                          \* - inspect the first pending message (by definition, the message with
                          \*   lowest clock from that client)
                          \* - extract the timestamp from the message
                          \* - record the client and timestamp in case this is the "oldest" message

                          firstPending := Head(pendingRequests[client]);
                          assert(firstPending.op = GET_MSG \/ firstPending.op = PUT_MSG);
                          timestamp := firstPending.timestamp;

                          \* a message is only stable if its timestamp is lower than
                          \* minClock
                          if (timestamp < minClock) {

                              \* this is the next stable message if it has the lowest
                              \* timestamp seen so far; if the timestamp is the same as
                              \* the lowest seen so far, do a client-id comparison
                              chooseMessage := (timestamp < lowestPending) \/ ((timestamp = lowestPending) /\ (client < nextClient));
                              if (chooseMessage) {
                                  nextClient := client;
                                  lowestPending := timestamp;
                              }
                          };

                          pendingClients := pendingClients \ {client};
                      }
                  };

                \* add the next stable message to the 'stableMessages' sequence.
                \* if 'lowestPending' is >= 'minClock', it means no more stable messages
                \* are pending, and we can leave this loop.
                addStableMessage:
                  if (lowestPending < minClock) {
                      msg := Head(pendingRequests[nextClient]);
                      pendingRequests[nextClient] := Tail(pendingRequests[nextClient]);

                      stableMessages := Append(stableMessages, msg);
                  } else {
                      continue := FALSE;
                  }
            };

          i := 1;

          \* iterate over our sequence of 'stableMessages' built in the previous
          \* step, responding to each of them in order.
          respondPendingRequestsLoop:
            while (i <= Len(stableMessages)) {
                msg := stableMessages[i];
                i := i + 1;

                respondStableGet:
                  if (msg.op = GET_MSG) {
                      key := msg.key;
                      val := kv[key];

                      \* send the value read from the database back to the client
                      clients[msg.reply_to] := [type |-> GET_RESPONSE, result |-> val];
                  };

                respondStablePut:
                  if (msg.op = PUT_MSG) {
                      key := msg.key;
                      val := msg.value;

                      \* update our database and send an OK back to the client
                      kv[key] := val;

                      clients[msg.reply_to] := [type |-> PUT_RESPONSE, result |-> ok];
                  };
            }
      }
  }

  \* Client Definitions
  \* ------------------
  \*
  \* The following archetypes define the client functions as specified in A1.
  \* Note that these operations are the "logical" versions of the API: for example,
  \* a Put archetype here sends a "Put" message to all replicas.
  \*
  \* In all of the definitions below, note that 'clocks' represent the client's
  \* logical clock. However, upon disconnection, the clock is set to '-1', and
  \* clients know to terminate when that happens.


  \* Specifies a Get request from a client. Arguments:
  \*
  \* - clientId: client identifier, used by the replica to identify which client is
  \*             performing the operation
  \* - replicas: connections to replica servers
  \* - clients: connections to clients. Used only to listen for incoming messages
  \*            from replicas (i.e., to send the value of the key being read).
  \* - key: the key being read. This *must* belong to the KeySpace set.
  \* - clock: The initial logical clock
  \*
  \* A Get message sent to the replica is a record in the following format:
  \*
  \*     [op: GET_MSG, key: key, client: client_id, timestamp: lamport_clock]
  archetype Get(ref clientId, ref replicas[_], ref clients[_], key, ref clock[_], spin, ref outside)
  variable continue = TRUE, getReq, getResp;
  {
      \* Loop until disconnected
      getLoop:
        while (continue) {
            getRequest:
              \* if disconnected, return
              if (clock[clientId] = -1) {
                  continue := FALSE
              } else {
                  \* increment the logical clock, and construct a valid
                  \* Get message.
                  clock[clientId] := clock[clientId] + 1;
                  getReq := [op |-> GET_MSG, key |-> key, client |-> clientId, timestamp |-> clock[clientId], reply_to |-> self];

                  \* Choose some replica from the set of replicas to send this
                  \* request to
                  with (dst \in ReplicaSet) {
                      replicas[dst] := getReq;
                  };

                  getReply:
                    if (clock[clientId] = -1) {
                        \* Client disconnected -- terminate
                        continue := FALSE;
                    } else {
                        \* Waits for the response from the replica
                        getResp := clients[self];
                        assert(getResp.type = GET_RESPONSE);
                        outside := getResp.result;
                    }
              };

            getCheckSpin:
              if (~spin) {
                  continue := FALSE;
              }
        }
  }

  \* Specifies a Put request from a client. Arguments:
  \*
  \* - clientId: client identifier, used by the replica to identify which client is
  \*             performing the operation
  \* - replicas: connection to the replicas.
  \* - clients: connection to the clients. Used to read incoming messages (response
  \*            from the Put request
  \* - key: the key being set.
  \* - value: the value being written to the key
  \* - clock: Lamport clocks
  \*
  \* A Put message sent to the replica is a record in the following format:
  \*
  \*     [op: PUT_MSG, key: key, value: value, client: client_id, timestamp: lamport_clock]
  archetype Put(ref clientId, ref replicas[_], ref clients[_], key, value, ref clock[_], spin, ref outside)
  variables continue = TRUE, i, j, putReq, putResp;
  {
      \* Loops indefinitely until disconnected
      putLoop:
        while (continue) {
            putRequest:
              \* if disconnected, return
              if (clock[clientId] = -1) {
                  continue := FALSE;
              } else {
                  \* increment the logical clock, construct the payload to be sent
                  \* to the replica, and set 'locked' to TRUE
                  clock[clientId] := clock[clientId] + 1;
                  putReq := [op |-> PUT_MSG, key |-> key, value |-> value, client |-> clientId, timestamp |-> clock[clientId], reply_to |-> self];
                  i := 0;
                  j := 0;

                  \* Put requests must be broadcast to all replicas
                  putBroadcast:
                    Broadcast(replicas, j, NUM_REPLICAS-1, putReq, clock[clientId]);

                  \* wait for a response from all replicas, and allow other
                  \* calls to the replica to happen after that.
                  putResponse:
                    while (i < Cardinality(ReplicaSet)) {
                        if (clock[clientId] = -1) {
                            continue := FALSE;
                            goto putLoop;
                        } else {
                            putResp := clients[self];
                            assert(putResp.type = PUT_RESPONSE);

                            i := i + 1;
                        }
                    };

                  putComplete:
                    outside := PUT_RESPONSE;
              };

            putCheckSpin:
              if (~spin) {
                  continue := FALSE;
              }
        }
  }

  \* Specifies a Disconnect message from the client.
  \*
  \* A Disconnect message sent to the replica is a record in the following format:
  \*
  \*     [op: DISCONNECT_MSG, client: client_id]
  archetype Disconnect(ref clientId, ref replicas[_], ref clock[_])
  variables msg, j;
  {
      sendDisconnectRequest:
        msg := [op |-> DISCONNECT_MSG, client |-> clientId];

        \* setting the logical clock internally to -1 indicates that this client
        \* has disconnected. Other operations terminate accordingly.
        clock[clientId] := -1;
        j := 0;

      \* Disconnection messages need to be broadcast to all replicas.
      \* "Clock" is set to zero because the replica is disconnected but we
      \* *do* want to broadcast that message
      disconnectBroadcast:
        Broadcast(replicas, j, NUM_REPLICAS-1, msg, 0);
  }

  \* Specifies a ClockUpdate ('null') message from the client.
  \* If the client has disconnected, no more clock updates are sent.
  \*
  \* A ClockUpdate message sent to the replica is a record in the following format:
  \*
  \*     [op: NULL_MSG, client: client_id, timestamp: logical_clock]
  archetype ClockUpdate(ref clientId, ref replicas[_], ref clock[_], spin)
  variables continue = TRUE, j, msg;
  {
      clockUpdateLoop:
        while (continue) {
            \* if we have disconnected, return
            if (clock[clientId] = -1) {
                continue := FALSE;
            } else {
                \* tick the lock and construct the message accordingly
                clock[clientId] := clock[clientId] + 1;
                msg := [op |-> NULL_MSG, client |-> clientId, timestamp |-> clock[clientId]];
                j := 0;

                nullBroadcast:
                  \* clock update messages must be broadcast to all replicas.
                  Broadcast(replicas, j, NUM_REPLICAS-1, msg, clock[clientId]);
            };

            nullCheckSpin:
              if (~spin) {
                  continue := FALSE;
              }
        }
  }

  \* Global Variables
  \* ----------------

  variables
            \* queue of incoming messages for each of the replicas
            replicasNetwork = [id \in ReplicaSet |-> <<>>],

            \* all clients performing operations in this model
            allClients = GetSet \cup PutSet \cup DisconnectSet \cup NullSet,

            \* queue of incoming messages for each of the clients
            clientMailboxes = [id \in allClients |-> <<>>],

            \* client identifier: to be appropriately mapped
            cid = 0,

            \* communication channel with the caller; astracted
            \* in this specification
            out = 0,

            \* all clocks set to 0 initially
            clocks = [c \in ClientSet |-> 0];


  \* Process Instantiations
  \* ----------------------
  \*
  \* This is where the archetypes defined above are instantiated into actual PlusCal
  \* processes. We instantiate NUM_REPLICAS replica servers and NUM_CLIENTS client
  \* processes for each possible client operation. TLC will be responsible for
  \* exploring the different orderings in which these clients and replicas
  \* may interact.


  \* Instantiate replica servers. The network model used is the one defined in
  \* the FIFOChannel mapping macro.
  fair process (Replica \in ReplicaSet) == instance AReplica(ref clientMailboxes[_], ref replicasNetwork[_], [k \in KeySpace |-> NULL])
      mapping @1[_] via FIFOChannel
      mapping @2[_] via FIFOChannel
      mapping @3[_] via Identity;

  \* Instantiate clients:

  fair process (GetClient \in GetSet) == instance Get(ref cid, ref replicasNetwork[_], ref clientMailboxes[_], GET_KEY, ref clocks[_], TRUE, ref out)
      mapping cid via GetClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientMailboxes[_] via FIFOChannel;

  fair process (PutClient \in PutSet) == instance Put(ref cid, ref replicasNetwork[_], ref clientMailboxes[_], PUT_KEY, PUT_VALUE, ref clocks[_], TRUE, ref out)
      mapping cid via PutClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientMailboxes[_] via FIFOChannel;

  fair process (DisconnectClient \in DisconnectSet) == instance Disconnect(ref cid, ref replicasNetwork[_], ref clocks[_])
      mapping cid via DisconnectClientId
      mapping replicasNetwork[_] via FIFOChannel;

  fair process (ClockUpdateClient \in NullSet) == instance ClockUpdate(ref cid, ref replicasNetwork[_], ref clocks[_], TRUE)
      mapping cid via NullClientId
      mapping replicasNetwork[_] via FIFOChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm ReplicatedKV {
    variables replicasNetwork = [id \in ReplicaSet |-> <<>>], allClients = (((GetSet) \cup (PutSet)) \cup (DisconnectSet)) \cup (NullSet), clientMailboxes = [id \in allClients |-> <<>>], cid = 0, out = 0, clocks = [c \in ClientSet |-> 0], replicasRead, replicasWrite, kvRead, clientsWrite, clientsWrite0, kvWrite, kvWrite0, clientsWrite1, clientsWrite2, kvWrite1, replicasWrite0, clientsWrite3, kvWrite2, clientIdRead, clockRead, clientIdRead0, clockRead0, clientIdRead1, clockWrite, keyRead, clientIdRead2, clientIdRead3, clockRead1, replicasWrite1, clientsRead, clientsWrite4, outsideWrite, clientsWrite5, outsideWrite0, clockWrite0, replicasWrite2, clientsWrite6, outsideWrite1, spinRead, clockWrite1, replicasWrite3, clientsWrite7, outsideWrite2, clientIdRead4, clockRead2, clientIdRead5, clockRead3, clientIdRead6, clockWrite2, keyRead0, valueRead, clientIdRead7, clientIdRead8, clockRead4, replicasWrite4, replicasWrite5, clientsRead0, clientsWrite8, clientsWrite9, clientsWrite10, outsideWrite3, clockWrite3, replicasWrite6, clientsWrite11, outsideWrite4, spinRead0, clockWrite4, replicasWrite7, clientsWrite12, outsideWrite5, clientIdRead9, clientIdRead10, clockWrite5, replicasWrite8, replicasWrite9, clientIdRead11, clockRead5, clientIdRead12, clockRead6, clientIdRead13, clockWrite6, clientIdRead14, clientIdRead15, clockRead7, replicasWrite10, replicasWrite11, clockWrite7, replicasWrite12, spinRead1, clockWrite8, replicasWrite13;
    define {
        NUM_NODES == (NUM_REPLICAS) + (NUM_CLIENTS)
        ReplicaSet == (0) .. ((NUM_REPLICAS) - (1))
        ClientSet == (NUM_REPLICAS) .. ((NUM_NODES) - (1))
    }
    fair process (Replica \in ReplicaSet)
    variables kvLocal = [k \in KeySpace |-> NULL], liveClients = ClientSet, pendingRequests = [c \in liveClients |-> <<>>], stableMessages = <<>>, i, firstPending, timestamp, nextClient, lowestPending, chooseMessage, currentClocks = [c \in liveClients |-> 0], minClock, continue, pendingClients, clientsIter, msg, ok, key, val;
    {
        replicaLoop:
            if (TRUE) {
                stableMessages := <<>>;
                continue := TRUE;
                receiveClientRequest:
                    await (Len(replicasNetwork[self])) > (0);
                    with (msg0 = Head(replicasNetwork[self])) {
                        replicasWrite := [replicasNetwork EXCEPT ![self] = Tail(replicasNetwork[self])];
                        replicasRead := msg0;
                    };
                    msg := replicasRead;
                    replicasNetwork := replicasWrite;
                
                clientDisconnected:
                    if (((msg).op) = (DISCONNECT_MSG)) {
                        liveClients := (liveClients) \ ({(msg).client});
                    };
                
                replicaGetRequest:
                    if (((msg).op) = (GET_MSG)) {
                        assert ((msg).client) \in (liveClients);
                        currentClocks[msg.client] := (msg).timestamp;
                        pendingRequests[msg.client] := Append(pendingRequests[(msg).client], msg);
                    };
                
                replicaPutRequest:
                    if (((msg).op) = (PUT_MSG)) {
                        currentClocks[msg.client] := (msg).timestamp;
                        pendingRequests[msg.client] := Append(pendingRequests[(msg).client], msg);
                    };
                
                replicaNullRequest:
                    if (((msg).op) = (NULL_MSG)) {
                        currentClocks[msg.client] := (msg).timestamp;
                    };
                
                findStableRequestsLoop:
                    if (continue) {
                        pendingClients := {c \in liveClients : (Len(pendingRequests[c])) > (0)};
                        nextClient := (NUM_NODES) + (1);
                        clientsIter := liveClients;
                        i := 0;
                        minClock := 0;
                        findMinClock:
                            if ((i) < (Cardinality(clientsIter))) {
                                with (client \in clientsIter) {
                                    if (((minClock) = (0)) \/ ((currentClocks[client]) < (minClock))) {
                                        minClock := currentClocks[client];
                                    };
                                    clientsIter := (clientsIter) \ ({client});
                                };
                                goto findMinClock;
                            } else {
                                lowestPending := (minClock) + (1);
                                i := 0;
                            };
                        
                        findMinClient:
                            if ((i) < (Cardinality(pendingClients))) {
                                with (client \in pendingClients) {
                                    firstPending := Head(pendingRequests[client]);
                                    assert (((firstPending).op) = (GET_MSG)) \/ (((firstPending).op) = (PUT_MSG));
                                    timestamp := (firstPending).timestamp;
                                    if ((timestamp) < (minClock)) {
                                        chooseMessage := ((timestamp) < (lowestPending)) \/ (((timestamp) = (lowestPending)) /\ ((client) < (nextClient)));
                                        if (chooseMessage) {
                                            nextClient := client;
                                            lowestPending := timestamp;
                                        };
                                    };
                                    pendingClients := (pendingClients) \ ({client});
                                };
                                goto findMinClient;
                            };
                        
                        addStableMessage:
                            if ((lowestPending) < (minClock)) {
                                msg := Head(pendingRequests[nextClient]);
                                pendingRequests[nextClient] := Tail(pendingRequests[nextClient]);
                                stableMessages := Append(stableMessages, msg);
                                goto findStableRequestsLoop;
                            } else {
                                continue := FALSE;
                                goto findStableRequestsLoop;
                            };
                    
                    } else {
                        i := 1;
                    };
                
                respondPendingRequestsLoop:
                    if ((i) <= (Len(stableMessages))) {
                        msg := stableMessages[i];
                        i := (i) + (1);
                        respondStableGet:
                            if (((msg).op) = (GET_MSG)) {
                                key := (msg).key;
                                kvRead := kvLocal[key];
                                val := kvRead;
                                await (Len(clientMailboxes[(msg).reply_to])) < (BUFFER_SIZE);
                                clientsWrite := [clientMailboxes EXCEPT ![(msg).reply_to] = Append(clientMailboxes[(msg).reply_to], [type |-> GET_RESPONSE, result |-> val])];
                                clientsWrite0 := clientsWrite;
                                clientMailboxes := clientsWrite0;
                            } else {
                                clientsWrite0 := clientMailboxes;
                                clientMailboxes := clientsWrite0;
                            };
                        
                        respondStablePut:
                            if (((msg).op) = (PUT_MSG)) {
                                key := (msg).key;
                                val := (msg).value;
                                kvWrite := [kvLocal EXCEPT ![key] = val];
                                await (Len(clientMailboxes[(msg).reply_to])) < (BUFFER_SIZE);
                                clientsWrite := [clientMailboxes EXCEPT ![(msg).reply_to] = Append(clientMailboxes[(msg).reply_to], [type |-> PUT_RESPONSE, result |-> ok])];
                                kvWrite0 := kvWrite;
                                clientsWrite1 := clientsWrite;
                                clientMailboxes := clientsWrite1;
                                kvLocal := kvWrite0;
                                goto respondPendingRequestsLoop;
                            } else {
                                kvWrite0 := kvLocal;
                                clientsWrite1 := clientMailboxes;
                                clientMailboxes := clientsWrite1;
                                kvLocal := kvWrite0;
                                goto respondPendingRequestsLoop;
                            };
                    
                    } else {
                        clientsWrite2 := clientMailboxes;
                        kvWrite1 := kvLocal;
                        clientMailboxes := clientsWrite2;
                        kvLocal := kvWrite1;
                        goto replicaLoop;
                    };
            
            } else {
                replicasWrite0 := replicasNetwork;
                clientsWrite3 := clientMailboxes;
                kvWrite2 := kvLocal;
                clientMailboxes := clientsWrite3;
                replicasNetwork := replicasWrite0;
                kvLocal := kvWrite2;
            };
    
    }
    fair process (GetClient \in GetSet)
    variables spinLocal = TRUE, continue = TRUE, getReq, getResp;
    {
        getLoop:
            if (continue) {
                getRequest:
                    clientIdRead := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                    clockRead := clocks[clientIdRead];
                    if ((clockRead) = (-(1))) {
                        continue := FALSE;
                        clockWrite0 := clocks;
                        replicasWrite2 := replicasNetwork;
                        clientsWrite6 := clientMailboxes;
                        outsideWrite1 := out;
                        replicasNetwork := replicasWrite2;
                        clientMailboxes := clientsWrite6;
                        clocks := clockWrite0;
                        out := outsideWrite1;
                    } else {
                        clientIdRead0 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                        clockRead0 := clocks[clientIdRead0];
                        clientIdRead1 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                        clockWrite := [clocks EXCEPT ![clientIdRead1] = (clockRead0) + (1)];
                        keyRead := GET_KEY;
                        clientIdRead2 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                        clientIdRead3 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                        clockRead1 := clockWrite[clientIdRead3];
                        getReq := [op |-> GET_MSG, key |-> keyRead, client |-> clientIdRead2, timestamp |-> clockRead1, reply_to |-> self];
                        with (dst \in ReplicaSet) {
                            await (Len(replicasNetwork[dst])) < (BUFFER_SIZE);
                            replicasWrite1 := [replicasNetwork EXCEPT ![dst] = Append(replicasNetwork[dst], getReq)];
                        };
                        replicasNetwork := replicasWrite1;
                        clocks := clockWrite;
                        getReply:
                            clientIdRead := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                            clockRead := clocks[clientIdRead];
                            if ((clockRead) = (-(1))) {
                                continue := FALSE;
                                clientsWrite5 := clientMailboxes;
                                outsideWrite0 := out;
                                clientMailboxes := clientsWrite5;
                                out := outsideWrite0;
                            } else {
                                await (Len(clientMailboxes[self])) > (0);
                                with (msg1 = Head(clientMailboxes[self])) {
                                    clientsWrite4 := [clientMailboxes EXCEPT ![self] = Tail(clientMailboxes[self])];
                                    clientsRead := msg1;
                                };
                                getResp := clientsRead;
                                assert ((getResp).type) = (GET_RESPONSE);
                                outsideWrite := (getResp).result;
                                clientsWrite5 := clientsWrite4;
                                outsideWrite0 := outsideWrite;
                                clientMailboxes := clientsWrite5;
                                out := outsideWrite0;
                            };
                    
                    };
                
                getCheckSpin:
                    spinRead := spinLocal;
                    if (~(spinRead)) {
                        continue := FALSE;
                        goto getLoop;
                    } else {
                        goto getLoop;
                    };
            
            } else {
                clockWrite1 := clocks;
                replicasWrite3 := replicasNetwork;
                clientsWrite7 := clientMailboxes;
                outsideWrite2 := out;
                replicasNetwork := replicasWrite3;
                clientMailboxes := clientsWrite7;
                clocks := clockWrite1;
                out := outsideWrite2;
            };
    
    }
    fair process (PutClient \in PutSet)
    variables spinLocal0 = TRUE, continue = TRUE, i, j, putReq, putResp;
    {
        putLoop:
            if (continue) {
                putRequest:
                    clientIdRead4 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                    clockRead2 := clocks[clientIdRead4];
                    if ((clockRead2) = (-(1))) {
                        continue := FALSE;
                        clockWrite3 := clocks;
                        replicasWrite6 := replicasNetwork;
                        clientsWrite11 := clientMailboxes;
                        outsideWrite4 := out;
                        replicasNetwork := replicasWrite6;
                        clientMailboxes := clientsWrite11;
                        clocks := clockWrite3;
                        out := outsideWrite4;
                    } else {
                        clientIdRead5 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                        clockRead3 := clocks[clientIdRead5];
                        clientIdRead6 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                        clockWrite2 := [clocks EXCEPT ![clientIdRead6] = (clockRead3) + (1)];
                        keyRead0 := PUT_KEY;
                        valueRead := PUT_VALUE;
                        clientIdRead7 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                        clientIdRead8 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                        clockRead4 := clockWrite2[clientIdRead8];
                        putReq := [op |-> PUT_MSG, key |-> keyRead0, value |-> valueRead, client |-> clientIdRead7, timestamp |-> clockRead4, reply_to |-> self];
                        i := 0;
                        j := 0;
                        clocks := clockWrite2;
                        putBroadcast:
                            clientIdRead4 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                            clockRead2 := clocks[clientIdRead4];
                            if (((j) <= ((NUM_REPLICAS) - (1))) /\ ((clockRead2) # (-(1)))) {
                                await (Len(replicasNetwork[j])) < (BUFFER_SIZE);
                                replicasWrite4 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], putReq)];
                                j := (j) + (1);
                                replicasWrite5 := replicasWrite4;
                                replicasNetwork := replicasWrite5;
                                goto putBroadcast;
                            } else {
                                replicasWrite5 := replicasNetwork;
                                replicasNetwork := replicasWrite5;
                            };
                        
                        putResponse:
                            if ((i) < (Cardinality(ReplicaSet))) {
                                clientIdRead4 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                                clockRead2 := clocks[clientIdRead4];
                                if ((clockRead2) = (-(1))) {
                                    continue := FALSE;
                                    clientsWrite9 := clientMailboxes;
                                    clientsWrite10 := clientsWrite9;
                                    clientMailboxes := clientsWrite10;
                                    goto putLoop;
                                } else {
                                    await (Len(clientMailboxes[self])) > (0);
                                    with (msg2 = Head(clientMailboxes[self])) {
                                        clientsWrite8 := [clientMailboxes EXCEPT ![self] = Tail(clientMailboxes[self])];
                                        clientsRead0 := msg2;
                                    };
                                    putResp := clientsRead0;
                                    assert ((putResp).type) = (PUT_RESPONSE);
                                    i := (i) + (1);
                                    clientsWrite9 := clientsWrite8;
                                    clientsWrite10 := clientsWrite9;
                                    clientMailboxes := clientsWrite10;
                                    goto putResponse;
                                };
                            } else {
                                clientsWrite10 := clientMailboxes;
                                clientMailboxes := clientsWrite10;
                            };
                        
                        putComplete:
                            outsideWrite3 := PUT_RESPONSE;
                            out := outsideWrite3;
                    
                    };
                
                putCheckSpin:
                    spinRead0 := spinLocal0;
                    if (~(spinRead0)) {
                        continue := FALSE;
                        goto putLoop;
                    } else {
                        goto putLoop;
                    };
            
            } else {
                clockWrite4 := clocks;
                replicasWrite7 := replicasNetwork;
                clientsWrite12 := clientMailboxes;
                outsideWrite5 := out;
                replicasNetwork := replicasWrite7;
                clientMailboxes := clientsWrite12;
                clocks := clockWrite4;
                out := outsideWrite5;
            };
    
    }
    fair process (DisconnectClient \in DisconnectSet)
    variables msg, j;
    {
        sendDisconnectRequest:
            clientIdRead9 := (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER));
            msg := [op |-> DISCONNECT_MSG, client |-> clientIdRead9];
            clientIdRead10 := (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER));
            clockWrite5 := [clocks EXCEPT ![clientIdRead10] = -(1)];
            j := 0;
            clocks := clockWrite5;
        disconnectBroadcast:
            if (((j) <= ((NUM_REPLICAS) - (1))) /\ ((0) # (-(1)))) {
                await (Len(replicasNetwork[j])) < (BUFFER_SIZE);
                replicasWrite8 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], msg)];
                j := (j) + (1);
                replicasWrite9 := replicasWrite8;
                replicasNetwork := replicasWrite9;
                goto disconnectBroadcast;
            } else {
                replicasWrite9 := replicasNetwork;
                replicasNetwork := replicasWrite9;
            };
    
    }
    fair process (ClockUpdateClient \in NullSet)
    variables spinLocal1 = TRUE, continue = TRUE, j, msg;
    {
        clockUpdateLoop:
            if (continue) {
                clientIdRead11 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                clockRead5 := clocks[clientIdRead11];
                if ((clockRead5) = (-(1))) {
                    continue := FALSE;
                    clockWrite7 := clocks;
                    replicasWrite12 := replicasNetwork;
                    replicasNetwork := replicasWrite12;
                    clocks := clockWrite7;
                } else {
                    clientIdRead12 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clockRead6 := clocks[clientIdRead12];
                    clientIdRead13 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clockWrite6 := [clocks EXCEPT ![clientIdRead13] = (clockRead6) + (1)];
                    clientIdRead14 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clientIdRead15 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clockRead7 := clockWrite6[clientIdRead15];
                    msg := [op |-> NULL_MSG, client |-> clientIdRead14, timestamp |-> clockRead7];
                    j := 0;
                    clocks := clockWrite6;
                    nullBroadcast:
                        clientIdRead11 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                        clockRead5 := clocks[clientIdRead11];
                        if (((j) <= ((NUM_REPLICAS) - (1))) /\ ((clockRead5) # (-(1)))) {
                            await (Len(replicasNetwork[j])) < (BUFFER_SIZE);
                            replicasWrite10 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], msg)];
                            j := (j) + (1);
                            replicasWrite11 := replicasWrite10;
                            replicasNetwork := replicasWrite11;
                            goto nullBroadcast;
                        } else {
                            replicasWrite11 := replicasNetwork;
                            replicasNetwork := replicasWrite11;
                        };
                
                };
                nullCheckSpin:
                    spinRead1 := spinLocal1;
                    if (~(spinRead1)) {
                        continue := FALSE;
                        goto clockUpdateLoop;
                    } else {
                        goto clockUpdateLoop;
                    };
            
            } else {
                clockWrite8 := clocks;
                replicasWrite13 := replicasNetwork;
                replicasNetwork := replicasWrite13;
                clocks := clockWrite8;
            };
    
    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-edda648b9b148ad88bcb79bb7a4a821b
\* Process variable i of process Replica at line 659 col 148 changed to i_
\* Process variable continue of process Replica at line 659 col 271 changed to continue_
\* Process variable msg of process Replica at line 659 col 310 changed to msg_
\* Process variable continue of process GetClient at line 808 col 33 changed to continue_G
\* Process variable continue of process PutClient at line 889 col 34 changed to continue_P
\* Process variable j of process PutClient at line 889 col 54 changed to j_
\* Process variable msg of process DisconnectClient at line 992 col 15 changed to msg_D
\* Process variable j of process DisconnectClient at line 992 col 20 changed to j_D
CONSTANT defaultInitValue
VARIABLES replicasNetwork, allClients, clientMailboxes, cid, out, clocks, 
          replicasRead, replicasWrite, kvRead, clientsWrite, clientsWrite0, 
          kvWrite, kvWrite0, clientsWrite1, clientsWrite2, kvWrite1, 
          replicasWrite0, clientsWrite3, kvWrite2, clientIdRead, clockRead, 
          clientIdRead0, clockRead0, clientIdRead1, clockWrite, keyRead, 
          clientIdRead2, clientIdRead3, clockRead1, replicasWrite1, 
          clientsRead, clientsWrite4, outsideWrite, clientsWrite5, 
          outsideWrite0, clockWrite0, replicasWrite2, clientsWrite6, 
          outsideWrite1, spinRead, clockWrite1, replicasWrite3, clientsWrite7, 
          outsideWrite2, clientIdRead4, clockRead2, clientIdRead5, clockRead3, 
          clientIdRead6, clockWrite2, keyRead0, valueRead, clientIdRead7, 
          clientIdRead8, clockRead4, replicasWrite4, replicasWrite5, 
          clientsRead0, clientsWrite8, clientsWrite9, clientsWrite10, 
          outsideWrite3, clockWrite3, replicasWrite6, clientsWrite11, 
          outsideWrite4, spinRead0, clockWrite4, replicasWrite7, 
          clientsWrite12, outsideWrite5, clientIdRead9, clientIdRead10, 
          clockWrite5, replicasWrite8, replicasWrite9, clientIdRead11, 
          clockRead5, clientIdRead12, clockRead6, clientIdRead13, clockWrite6, 
          clientIdRead14, clientIdRead15, clockRead7, replicasWrite10, 
          replicasWrite11, clockWrite7, replicasWrite12, spinRead1, 
          clockWrite8, replicasWrite13, pc

(* define statement *)
NUM_NODES == (NUM_REPLICAS) + (NUM_CLIENTS)
ReplicaSet == (0) .. ((NUM_REPLICAS) - (1))
ClientSet == (NUM_REPLICAS) .. ((NUM_NODES) - (1))

VARIABLES kvLocal, liveClients, pendingRequests, stableMessages, i_, 
          firstPending, timestamp, nextClient, lowestPending, chooseMessage, 
          currentClocks, minClock, continue_, pendingClients, clientsIter, 
          msg_, ok, key, val, spinLocal, continue_G, getReq, getResp, 
          spinLocal0, continue_P, i, j_, putReq, putResp, msg_D, j_D, 
          spinLocal1, continue, j, msg

vars == << replicasNetwork, allClients, clientMailboxes, cid, out, clocks, 
           replicasRead, replicasWrite, kvRead, clientsWrite, clientsWrite0, 
           kvWrite, kvWrite0, clientsWrite1, clientsWrite2, kvWrite1, 
           replicasWrite0, clientsWrite3, kvWrite2, clientIdRead, clockRead, 
           clientIdRead0, clockRead0, clientIdRead1, clockWrite, keyRead, 
           clientIdRead2, clientIdRead3, clockRead1, replicasWrite1, 
           clientsRead, clientsWrite4, outsideWrite, clientsWrite5, 
           outsideWrite0, clockWrite0, replicasWrite2, clientsWrite6, 
           outsideWrite1, spinRead, clockWrite1, replicasWrite3, 
           clientsWrite7, outsideWrite2, clientIdRead4, clockRead2, 
           clientIdRead5, clockRead3, clientIdRead6, clockWrite2, keyRead0, 
           valueRead, clientIdRead7, clientIdRead8, clockRead4, 
           replicasWrite4, replicasWrite5, clientsRead0, clientsWrite8, 
           clientsWrite9, clientsWrite10, outsideWrite3, clockWrite3, 
           replicasWrite6, clientsWrite11, outsideWrite4, spinRead0, 
           clockWrite4, replicasWrite7, clientsWrite12, outsideWrite5, 
           clientIdRead9, clientIdRead10, clockWrite5, replicasWrite8, 
           replicasWrite9, clientIdRead11, clockRead5, clientIdRead12, 
           clockRead6, clientIdRead13, clockWrite6, clientIdRead14, 
           clientIdRead15, clockRead7, replicasWrite10, replicasWrite11, 
           clockWrite7, replicasWrite12, spinRead1, clockWrite8, 
           replicasWrite13, pc, kvLocal, liveClients, pendingRequests, 
           stableMessages, i_, firstPending, timestamp, nextClient, 
           lowestPending, chooseMessage, currentClocks, minClock, continue_, 
           pendingClients, clientsIter, msg_, ok, key, val, spinLocal, 
           continue_G, getReq, getResp, spinLocal0, continue_P, i, j_, putReq, 
           putResp, msg_D, j_D, spinLocal1, continue, j, msg >>

ProcSet == (ReplicaSet) \cup (GetSet) \cup (PutSet) \cup (DisconnectSet) \cup (NullSet)

Init == (* Global variables *)
        /\ replicasNetwork = [id \in ReplicaSet |-> <<>>]
        /\ allClients = ((((GetSet) \cup (PutSet)) \cup (DisconnectSet)) \cup (NullSet))
        /\ clientMailboxes = [id \in allClients |-> <<>>]
        /\ cid = 0
        /\ out = 0
        /\ clocks = [c \in ClientSet |-> 0]
        /\ replicasRead = defaultInitValue
        /\ replicasWrite = defaultInitValue
        /\ kvRead = defaultInitValue
        /\ clientsWrite = defaultInitValue
        /\ clientsWrite0 = defaultInitValue
        /\ kvWrite = defaultInitValue
        /\ kvWrite0 = defaultInitValue
        /\ clientsWrite1 = defaultInitValue
        /\ clientsWrite2 = defaultInitValue
        /\ kvWrite1 = defaultInitValue
        /\ replicasWrite0 = defaultInitValue
        /\ clientsWrite3 = defaultInitValue
        /\ kvWrite2 = defaultInitValue
        /\ clientIdRead = defaultInitValue
        /\ clockRead = defaultInitValue
        /\ clientIdRead0 = defaultInitValue
        /\ clockRead0 = defaultInitValue
        /\ clientIdRead1 = defaultInitValue
        /\ clockWrite = defaultInitValue
        /\ keyRead = defaultInitValue
        /\ clientIdRead2 = defaultInitValue
        /\ clientIdRead3 = defaultInitValue
        /\ clockRead1 = defaultInitValue
        /\ replicasWrite1 = defaultInitValue
        /\ clientsRead = defaultInitValue
        /\ clientsWrite4 = defaultInitValue
        /\ outsideWrite = defaultInitValue
        /\ clientsWrite5 = defaultInitValue
        /\ outsideWrite0 = defaultInitValue
        /\ clockWrite0 = defaultInitValue
        /\ replicasWrite2 = defaultInitValue
        /\ clientsWrite6 = defaultInitValue
        /\ outsideWrite1 = defaultInitValue
        /\ spinRead = defaultInitValue
        /\ clockWrite1 = defaultInitValue
        /\ replicasWrite3 = defaultInitValue
        /\ clientsWrite7 = defaultInitValue
        /\ outsideWrite2 = defaultInitValue
        /\ clientIdRead4 = defaultInitValue
        /\ clockRead2 = defaultInitValue
        /\ clientIdRead5 = defaultInitValue
        /\ clockRead3 = defaultInitValue
        /\ clientIdRead6 = defaultInitValue
        /\ clockWrite2 = defaultInitValue
        /\ keyRead0 = defaultInitValue
        /\ valueRead = defaultInitValue
        /\ clientIdRead7 = defaultInitValue
        /\ clientIdRead8 = defaultInitValue
        /\ clockRead4 = defaultInitValue
        /\ replicasWrite4 = defaultInitValue
        /\ replicasWrite5 = defaultInitValue
        /\ clientsRead0 = defaultInitValue
        /\ clientsWrite8 = defaultInitValue
        /\ clientsWrite9 = defaultInitValue
        /\ clientsWrite10 = defaultInitValue
        /\ outsideWrite3 = defaultInitValue
        /\ clockWrite3 = defaultInitValue
        /\ replicasWrite6 = defaultInitValue
        /\ clientsWrite11 = defaultInitValue
        /\ outsideWrite4 = defaultInitValue
        /\ spinRead0 = defaultInitValue
        /\ clockWrite4 = defaultInitValue
        /\ replicasWrite7 = defaultInitValue
        /\ clientsWrite12 = defaultInitValue
        /\ outsideWrite5 = defaultInitValue
        /\ clientIdRead9 = defaultInitValue
        /\ clientIdRead10 = defaultInitValue
        /\ clockWrite5 = defaultInitValue
        /\ replicasWrite8 = defaultInitValue
        /\ replicasWrite9 = defaultInitValue
        /\ clientIdRead11 = defaultInitValue
        /\ clockRead5 = defaultInitValue
        /\ clientIdRead12 = defaultInitValue
        /\ clockRead6 = defaultInitValue
        /\ clientIdRead13 = defaultInitValue
        /\ clockWrite6 = defaultInitValue
        /\ clientIdRead14 = defaultInitValue
        /\ clientIdRead15 = defaultInitValue
        /\ clockRead7 = defaultInitValue
        /\ replicasWrite10 = defaultInitValue
        /\ replicasWrite11 = defaultInitValue
        /\ clockWrite7 = defaultInitValue
        /\ replicasWrite12 = defaultInitValue
        /\ spinRead1 = defaultInitValue
        /\ clockWrite8 = defaultInitValue
        /\ replicasWrite13 = defaultInitValue
        (* Process Replica *)
        /\ kvLocal = [self \in ReplicaSet |-> [k \in KeySpace |-> NULL]]
        /\ liveClients = [self \in ReplicaSet |-> ClientSet]
        /\ pendingRequests = [self \in ReplicaSet |-> [c \in liveClients[self] |-> <<>>]]
        /\ stableMessages = [self \in ReplicaSet |-> <<>>]
        /\ i_ = [self \in ReplicaSet |-> defaultInitValue]
        /\ firstPending = [self \in ReplicaSet |-> defaultInitValue]
        /\ timestamp = [self \in ReplicaSet |-> defaultInitValue]
        /\ nextClient = [self \in ReplicaSet |-> defaultInitValue]
        /\ lowestPending = [self \in ReplicaSet |-> defaultInitValue]
        /\ chooseMessage = [self \in ReplicaSet |-> defaultInitValue]
        /\ currentClocks = [self \in ReplicaSet |-> [c \in liveClients[self] |-> 0]]
        /\ minClock = [self \in ReplicaSet |-> defaultInitValue]
        /\ continue_ = [self \in ReplicaSet |-> defaultInitValue]
        /\ pendingClients = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsIter = [self \in ReplicaSet |-> defaultInitValue]
        /\ msg_ = [self \in ReplicaSet |-> defaultInitValue]
        /\ ok = [self \in ReplicaSet |-> defaultInitValue]
        /\ key = [self \in ReplicaSet |-> defaultInitValue]
        /\ val = [self \in ReplicaSet |-> defaultInitValue]
        (* Process GetClient *)
        /\ spinLocal = [self \in GetSet |-> TRUE]
        /\ continue_G = [self \in GetSet |-> TRUE]
        /\ getReq = [self \in GetSet |-> defaultInitValue]
        /\ getResp = [self \in GetSet |-> defaultInitValue]
        (* Process PutClient *)
        /\ spinLocal0 = [self \in PutSet |-> TRUE]
        /\ continue_P = [self \in PutSet |-> TRUE]
        /\ i = [self \in PutSet |-> defaultInitValue]
        /\ j_ = [self \in PutSet |-> defaultInitValue]
        /\ putReq = [self \in PutSet |-> defaultInitValue]
        /\ putResp = [self \in PutSet |-> defaultInitValue]
        (* Process DisconnectClient *)
        /\ msg_D = [self \in DisconnectSet |-> defaultInitValue]
        /\ j_D = [self \in DisconnectSet |-> defaultInitValue]
        (* Process ClockUpdateClient *)
        /\ spinLocal1 = [self \in NullSet |-> TRUE]
        /\ continue = [self \in NullSet |-> TRUE]
        /\ j = [self \in NullSet |-> defaultInitValue]
        /\ msg = [self \in NullSet |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in ReplicaSet -> "replicaLoop"
                                        [] self \in GetSet -> "getLoop"
                                        [] self \in PutSet -> "putLoop"
                                        [] self \in DisconnectSet -> "sendDisconnectRequest"
                                        [] self \in NullSet -> "clockUpdateLoop"]

replicaLoop(self) == /\ pc[self] = "replicaLoop"
                     /\ IF TRUE
                           THEN /\ stableMessages' = [stableMessages EXCEPT ![self] = <<>>]
                                /\ continue_' = [continue_ EXCEPT ![self] = TRUE]
                                /\ pc' = [pc EXCEPT ![self] = "receiveClientRequest"]
                                /\ UNCHANGED << replicasNetwork, 
                                                clientMailboxes, 
                                                replicasWrite0, clientsWrite3, 
                                                kvWrite2, kvLocal >>
                           ELSE /\ replicasWrite0' = replicasNetwork
                                /\ clientsWrite3' = clientMailboxes
                                /\ kvWrite2' = kvLocal[self]
                                /\ clientMailboxes' = clientsWrite3'
                                /\ replicasNetwork' = replicasWrite0'
                                /\ kvLocal' = [kvLocal EXCEPT ![self] = kvWrite2']
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << stableMessages, continue_ >>
                     /\ UNCHANGED << allClients, cid, out, clocks, 
                                     replicasRead, replicasWrite, kvRead, 
                                     clientsWrite, clientsWrite0, kvWrite, 
                                     kvWrite0, clientsWrite1, clientsWrite2, 
                                     kvWrite1, clientIdRead, clockRead, 
                                     clientIdRead0, clockRead0, clientIdRead1, 
                                     clockWrite, keyRead, clientIdRead2, 
                                     clientIdRead3, clockRead1, replicasWrite1, 
                                     clientsRead, clientsWrite4, outsideWrite, 
                                     clientsWrite5, outsideWrite0, clockWrite0, 
                                     replicasWrite2, clientsWrite6, 
                                     outsideWrite1, spinRead, clockWrite1, 
                                     replicasWrite3, clientsWrite7, 
                                     outsideWrite2, clientIdRead4, clockRead2, 
                                     clientIdRead5, clockRead3, clientIdRead6, 
                                     clockWrite2, keyRead0, valueRead, 
                                     clientIdRead7, clientIdRead8, clockRead4, 
                                     replicasWrite4, replicasWrite5, 
                                     clientsRead0, clientsWrite8, 
                                     clientsWrite9, clientsWrite10, 
                                     outsideWrite3, clockWrite3, 
                                     replicasWrite6, clientsWrite11, 
                                     outsideWrite4, spinRead0, clockWrite4, 
                                     replicasWrite7, clientsWrite12, 
                                     outsideWrite5, clientIdRead9, 
                                     clientIdRead10, clockWrite5, 
                                     replicasWrite8, replicasWrite9, 
                                     clientIdRead11, clockRead5, 
                                     clientIdRead12, clockRead6, 
                                     clientIdRead13, clockWrite6, 
                                     clientIdRead14, clientIdRead15, 
                                     clockRead7, replicasWrite10, 
                                     replicasWrite11, clockWrite7, 
                                     replicasWrite12, spinRead1, clockWrite8, 
                                     replicasWrite13, liveClients, 
                                     pendingRequests, i_, firstPending, 
                                     timestamp, nextClient, lowestPending, 
                                     chooseMessage, currentClocks, minClock, 
                                     pendingClients, clientsIter, msg_, ok, 
                                     key, val, spinLocal, continue_G, getReq, 
                                     getResp, spinLocal0, continue_P, i, j_, 
                                     putReq, putResp, msg_D, j_D, spinLocal1, 
                                     continue, j, msg >>

receiveClientRequest(self) == /\ pc[self] = "receiveClientRequest"
                              /\ (Len(replicasNetwork[self])) > (0)
                              /\ LET msg0 == Head(replicasNetwork[self]) IN
                                   /\ replicasWrite' = [replicasNetwork EXCEPT ![self] = Tail(replicasNetwork[self])]
                                   /\ replicasRead' = msg0
                              /\ msg_' = [msg_ EXCEPT ![self] = replicasRead']
                              /\ replicasNetwork' = replicasWrite'
                              /\ pc' = [pc EXCEPT ![self] = "clientDisconnected"]
                              /\ UNCHANGED << allClients, clientMailboxes, cid, 
                                              out, clocks, kvRead, 
                                              clientsWrite, clientsWrite0, 
                                              kvWrite, kvWrite0, clientsWrite1, 
                                              clientsWrite2, kvWrite1, 
                                              replicasWrite0, clientsWrite3, 
                                              kvWrite2, clientIdRead, 
                                              clockRead, clientIdRead0, 
                                              clockRead0, clientIdRead1, 
                                              clockWrite, keyRead, 
                                              clientIdRead2, clientIdRead3, 
                                              clockRead1, replicasWrite1, 
                                              clientsRead, clientsWrite4, 
                                              outsideWrite, clientsWrite5, 
                                              outsideWrite0, clockWrite0, 
                                              replicasWrite2, clientsWrite6, 
                                              outsideWrite1, spinRead, 
                                              clockWrite1, replicasWrite3, 
                                              clientsWrite7, outsideWrite2, 
                                              clientIdRead4, clockRead2, 
                                              clientIdRead5, clockRead3, 
                                              clientIdRead6, clockWrite2, 
                                              keyRead0, valueRead, 
                                              clientIdRead7, clientIdRead8, 
                                              clockRead4, replicasWrite4, 
                                              replicasWrite5, clientsRead0, 
                                              clientsWrite8, clientsWrite9, 
                                              clientsWrite10, outsideWrite3, 
                                              clockWrite3, replicasWrite6, 
                                              clientsWrite11, outsideWrite4, 
                                              spinRead0, clockWrite4, 
                                              replicasWrite7, clientsWrite12, 
                                              outsideWrite5, clientIdRead9, 
                                              clientIdRead10, clockWrite5, 
                                              replicasWrite8, replicasWrite9, 
                                              clientIdRead11, clockRead5, 
                                              clientIdRead12, clockRead6, 
                                              clientIdRead13, clockWrite6, 
                                              clientIdRead14, clientIdRead15, 
                                              clockRead7, replicasWrite10, 
                                              replicasWrite11, clockWrite7, 
                                              replicasWrite12, spinRead1, 
                                              clockWrite8, replicasWrite13, 
                                              kvLocal, liveClients, 
                                              pendingRequests, stableMessages, 
                                              i_, firstPending, timestamp, 
                                              nextClient, lowestPending, 
                                              chooseMessage, currentClocks, 
                                              minClock, continue_, 
                                              pendingClients, clientsIter, ok, 
                                              key, val, spinLocal, continue_G, 
                                              getReq, getResp, spinLocal0, 
                                              continue_P, i, j_, putReq, 
                                              putResp, msg_D, j_D, spinLocal1, 
                                              continue, j, msg >>

clientDisconnected(self) == /\ pc[self] = "clientDisconnected"
                            /\ IF ((msg_[self]).op) = (DISCONNECT_MSG)
                                  THEN /\ liveClients' = [liveClients EXCEPT ![self] = (liveClients[self]) \ ({(msg_[self]).client})]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED liveClients
                            /\ pc' = [pc EXCEPT ![self] = "replicaGetRequest"]
                            /\ UNCHANGED << replicasNetwork, allClients, 
                                            clientMailboxes, cid, out, clocks, 
                                            replicasRead, replicasWrite, 
                                            kvRead, clientsWrite, 
                                            clientsWrite0, kvWrite, kvWrite0, 
                                            clientsWrite1, clientsWrite2, 
                                            kvWrite1, replicasWrite0, 
                                            clientsWrite3, kvWrite2, 
                                            clientIdRead, clockRead, 
                                            clientIdRead0, clockRead0, 
                                            clientIdRead1, clockWrite, keyRead, 
                                            clientIdRead2, clientIdRead3, 
                                            clockRead1, replicasWrite1, 
                                            clientsRead, clientsWrite4, 
                                            outsideWrite, clientsWrite5, 
                                            outsideWrite0, clockWrite0, 
                                            replicasWrite2, clientsWrite6, 
                                            outsideWrite1, spinRead, 
                                            clockWrite1, replicasWrite3, 
                                            clientsWrite7, outsideWrite2, 
                                            clientIdRead4, clockRead2, 
                                            clientIdRead5, clockRead3, 
                                            clientIdRead6, clockWrite2, 
                                            keyRead0, valueRead, clientIdRead7, 
                                            clientIdRead8, clockRead4, 
                                            replicasWrite4, replicasWrite5, 
                                            clientsRead0, clientsWrite8, 
                                            clientsWrite9, clientsWrite10, 
                                            outsideWrite3, clockWrite3, 
                                            replicasWrite6, clientsWrite11, 
                                            outsideWrite4, spinRead0, 
                                            clockWrite4, replicasWrite7, 
                                            clientsWrite12, outsideWrite5, 
                                            clientIdRead9, clientIdRead10, 
                                            clockWrite5, replicasWrite8, 
                                            replicasWrite9, clientIdRead11, 
                                            clockRead5, clientIdRead12, 
                                            clockRead6, clientIdRead13, 
                                            clockWrite6, clientIdRead14, 
                                            clientIdRead15, clockRead7, 
                                            replicasWrite10, replicasWrite11, 
                                            clockWrite7, replicasWrite12, 
                                            spinRead1, clockWrite8, 
                                            replicasWrite13, kvLocal, 
                                            pendingRequests, stableMessages, 
                                            i_, firstPending, timestamp, 
                                            nextClient, lowestPending, 
                                            chooseMessage, currentClocks, 
                                            minClock, continue_, 
                                            pendingClients, clientsIter, msg_, 
                                            ok, key, val, spinLocal, 
                                            continue_G, getReq, getResp, 
                                            spinLocal0, continue_P, i, j_, 
                                            putReq, putResp, msg_D, j_D, 
                                            spinLocal1, continue, j, msg >>

replicaGetRequest(self) == /\ pc[self] = "replicaGetRequest"
                           /\ IF ((msg_[self]).op) = (GET_MSG)
                                 THEN /\ Assert(((msg_[self]).client) \in (liveClients[self]), 
                                                "Failure of assertion at line 681, column 25.")
                                      /\ currentClocks' = [currentClocks EXCEPT ![self][msg_[self].client] = (msg_[self]).timestamp]
                                      /\ pendingRequests' = [pendingRequests EXCEPT ![self][msg_[self].client] = Append(pendingRequests[self][(msg_[self]).client], msg_[self])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << pendingRequests, 
                                                      currentClocks >>
                           /\ pc' = [pc EXCEPT ![self] = "replicaPutRequest"]
                           /\ UNCHANGED << replicasNetwork, allClients, 
                                           clientMailboxes, cid, out, clocks, 
                                           replicasRead, replicasWrite, kvRead, 
                                           clientsWrite, clientsWrite0, 
                                           kvWrite, kvWrite0, clientsWrite1, 
                                           clientsWrite2, kvWrite1, 
                                           replicasWrite0, clientsWrite3, 
                                           kvWrite2, clientIdRead, clockRead, 
                                           clientIdRead0, clockRead0, 
                                           clientIdRead1, clockWrite, keyRead, 
                                           clientIdRead2, clientIdRead3, 
                                           clockRead1, replicasWrite1, 
                                           clientsRead, clientsWrite4, 
                                           outsideWrite, clientsWrite5, 
                                           outsideWrite0, clockWrite0, 
                                           replicasWrite2, clientsWrite6, 
                                           outsideWrite1, spinRead, 
                                           clockWrite1, replicasWrite3, 
                                           clientsWrite7, outsideWrite2, 
                                           clientIdRead4, clockRead2, 
                                           clientIdRead5, clockRead3, 
                                           clientIdRead6, clockWrite2, 
                                           keyRead0, valueRead, clientIdRead7, 
                                           clientIdRead8, clockRead4, 
                                           replicasWrite4, replicasWrite5, 
                                           clientsRead0, clientsWrite8, 
                                           clientsWrite9, clientsWrite10, 
                                           outsideWrite3, clockWrite3, 
                                           replicasWrite6, clientsWrite11, 
                                           outsideWrite4, spinRead0, 
                                           clockWrite4, replicasWrite7, 
                                           clientsWrite12, outsideWrite5, 
                                           clientIdRead9, clientIdRead10, 
                                           clockWrite5, replicasWrite8, 
                                           replicasWrite9, clientIdRead11, 
                                           clockRead5, clientIdRead12, 
                                           clockRead6, clientIdRead13, 
                                           clockWrite6, clientIdRead14, 
                                           clientIdRead15, clockRead7, 
                                           replicasWrite10, replicasWrite11, 
                                           clockWrite7, replicasWrite12, 
                                           spinRead1, clockWrite8, 
                                           replicasWrite13, kvLocal, 
                                           liveClients, stableMessages, i_, 
                                           firstPending, timestamp, nextClient, 
                                           lowestPending, chooseMessage, 
                                           minClock, continue_, pendingClients, 
                                           clientsIter, msg_, ok, key, val, 
                                           spinLocal, continue_G, getReq, 
                                           getResp, spinLocal0, continue_P, i, 
                                           j_, putReq, putResp, msg_D, j_D, 
                                           spinLocal1, continue, j, msg >>

replicaPutRequest(self) == /\ pc[self] = "replicaPutRequest"
                           /\ IF ((msg_[self]).op) = (PUT_MSG)
                                 THEN /\ currentClocks' = [currentClocks EXCEPT ![self][msg_[self].client] = (msg_[self]).timestamp]
                                      /\ pendingRequests' = [pendingRequests EXCEPT ![self][msg_[self].client] = Append(pendingRequests[self][(msg_[self]).client], msg_[self])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << pendingRequests, 
                                                      currentClocks >>
                           /\ pc' = [pc EXCEPT ![self] = "replicaNullRequest"]
                           /\ UNCHANGED << replicasNetwork, allClients, 
                                           clientMailboxes, cid, out, clocks, 
                                           replicasRead, replicasWrite, kvRead, 
                                           clientsWrite, clientsWrite0, 
                                           kvWrite, kvWrite0, clientsWrite1, 
                                           clientsWrite2, kvWrite1, 
                                           replicasWrite0, clientsWrite3, 
                                           kvWrite2, clientIdRead, clockRead, 
                                           clientIdRead0, clockRead0, 
                                           clientIdRead1, clockWrite, keyRead, 
                                           clientIdRead2, clientIdRead3, 
                                           clockRead1, replicasWrite1, 
                                           clientsRead, clientsWrite4, 
                                           outsideWrite, clientsWrite5, 
                                           outsideWrite0, clockWrite0, 
                                           replicasWrite2, clientsWrite6, 
                                           outsideWrite1, spinRead, 
                                           clockWrite1, replicasWrite3, 
                                           clientsWrite7, outsideWrite2, 
                                           clientIdRead4, clockRead2, 
                                           clientIdRead5, clockRead3, 
                                           clientIdRead6, clockWrite2, 
                                           keyRead0, valueRead, clientIdRead7, 
                                           clientIdRead8, clockRead4, 
                                           replicasWrite4, replicasWrite5, 
                                           clientsRead0, clientsWrite8, 
                                           clientsWrite9, clientsWrite10, 
                                           outsideWrite3, clockWrite3, 
                                           replicasWrite6, clientsWrite11, 
                                           outsideWrite4, spinRead0, 
                                           clockWrite4, replicasWrite7, 
                                           clientsWrite12, outsideWrite5, 
                                           clientIdRead9, clientIdRead10, 
                                           clockWrite5, replicasWrite8, 
                                           replicasWrite9, clientIdRead11, 
                                           clockRead5, clientIdRead12, 
                                           clockRead6, clientIdRead13, 
                                           clockWrite6, clientIdRead14, 
                                           clientIdRead15, clockRead7, 
                                           replicasWrite10, replicasWrite11, 
                                           clockWrite7, replicasWrite12, 
                                           spinRead1, clockWrite8, 
                                           replicasWrite13, kvLocal, 
                                           liveClients, stableMessages, i_, 
                                           firstPending, timestamp, nextClient, 
                                           lowestPending, chooseMessage, 
                                           minClock, continue_, pendingClients, 
                                           clientsIter, msg_, ok, key, val, 
                                           spinLocal, continue_G, getReq, 
                                           getResp, spinLocal0, continue_P, i, 
                                           j_, putReq, putResp, msg_D, j_D, 
                                           spinLocal1, continue, j, msg >>

replicaNullRequest(self) == /\ pc[self] = "replicaNullRequest"
                            /\ IF ((msg_[self]).op) = (NULL_MSG)
                                  THEN /\ currentClocks' = [currentClocks EXCEPT ![self][msg_[self].client] = (msg_[self]).timestamp]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED currentClocks
                            /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                            /\ UNCHANGED << replicasNetwork, allClients, 
                                            clientMailboxes, cid, out, clocks, 
                                            replicasRead, replicasWrite, 
                                            kvRead, clientsWrite, 
                                            clientsWrite0, kvWrite, kvWrite0, 
                                            clientsWrite1, clientsWrite2, 
                                            kvWrite1, replicasWrite0, 
                                            clientsWrite3, kvWrite2, 
                                            clientIdRead, clockRead, 
                                            clientIdRead0, clockRead0, 
                                            clientIdRead1, clockWrite, keyRead, 
                                            clientIdRead2, clientIdRead3, 
                                            clockRead1, replicasWrite1, 
                                            clientsRead, clientsWrite4, 
                                            outsideWrite, clientsWrite5, 
                                            outsideWrite0, clockWrite0, 
                                            replicasWrite2, clientsWrite6, 
                                            outsideWrite1, spinRead, 
                                            clockWrite1, replicasWrite3, 
                                            clientsWrite7, outsideWrite2, 
                                            clientIdRead4, clockRead2, 
                                            clientIdRead5, clockRead3, 
                                            clientIdRead6, clockWrite2, 
                                            keyRead0, valueRead, clientIdRead7, 
                                            clientIdRead8, clockRead4, 
                                            replicasWrite4, replicasWrite5, 
                                            clientsRead0, clientsWrite8, 
                                            clientsWrite9, clientsWrite10, 
                                            outsideWrite3, clockWrite3, 
                                            replicasWrite6, clientsWrite11, 
                                            outsideWrite4, spinRead0, 
                                            clockWrite4, replicasWrite7, 
                                            clientsWrite12, outsideWrite5, 
                                            clientIdRead9, clientIdRead10, 
                                            clockWrite5, replicasWrite8, 
                                            replicasWrite9, clientIdRead11, 
                                            clockRead5, clientIdRead12, 
                                            clockRead6, clientIdRead13, 
                                            clockWrite6, clientIdRead14, 
                                            clientIdRead15, clockRead7, 
                                            replicasWrite10, replicasWrite11, 
                                            clockWrite7, replicasWrite12, 
                                            spinRead1, clockWrite8, 
                                            replicasWrite13, kvLocal, 
                                            liveClients, pendingRequests, 
                                            stableMessages, i_, firstPending, 
                                            timestamp, nextClient, 
                                            lowestPending, chooseMessage, 
                                            minClock, continue_, 
                                            pendingClients, clientsIter, msg_, 
                                            ok, key, val, spinLocal, 
                                            continue_G, getReq, getResp, 
                                            spinLocal0, continue_P, i, j_, 
                                            putReq, putResp, msg_D, j_D, 
                                            spinLocal1, continue, j, msg >>

findStableRequestsLoop(self) == /\ pc[self] = "findStableRequestsLoop"
                                /\ IF continue_[self]
                                      THEN /\ pendingClients' = [pendingClients EXCEPT ![self] = {c \in liveClients[self] : (Len(pendingRequests[self][c])) > (0)}]
                                           /\ nextClient' = [nextClient EXCEPT ![self] = (NUM_NODES) + (1)]
                                           /\ clientsIter' = [clientsIter EXCEPT ![self] = liveClients[self]]
                                           /\ i_' = [i_ EXCEPT ![self] = 0]
                                           /\ minClock' = [minClock EXCEPT ![self] = 0]
                                           /\ pc' = [pc EXCEPT ![self] = "findMinClock"]
                                      ELSE /\ i_' = [i_ EXCEPT ![self] = 1]
                                           /\ pc' = [pc EXCEPT ![self] = "respondPendingRequestsLoop"]
                                           /\ UNCHANGED << nextClient, 
                                                           minClock, 
                                                           pendingClients, 
                                                           clientsIter >>
                                /\ UNCHANGED << replicasNetwork, allClients, 
                                                clientMailboxes, cid, out, 
                                                clocks, replicasRead, 
                                                replicasWrite, kvRead, 
                                                clientsWrite, clientsWrite0, 
                                                kvWrite, kvWrite0, 
                                                clientsWrite1, clientsWrite2, 
                                                kvWrite1, replicasWrite0, 
                                                clientsWrite3, kvWrite2, 
                                                clientIdRead, clockRead, 
                                                clientIdRead0, clockRead0, 
                                                clientIdRead1, clockWrite, 
                                                keyRead, clientIdRead2, 
                                                clientIdRead3, clockRead1, 
                                                replicasWrite1, clientsRead, 
                                                clientsWrite4, outsideWrite, 
                                                clientsWrite5, outsideWrite0, 
                                                clockWrite0, replicasWrite2, 
                                                clientsWrite6, outsideWrite1, 
                                                spinRead, clockWrite1, 
                                                replicasWrite3, clientsWrite7, 
                                                outsideWrite2, clientIdRead4, 
                                                clockRead2, clientIdRead5, 
                                                clockRead3, clientIdRead6, 
                                                clockWrite2, keyRead0, 
                                                valueRead, clientIdRead7, 
                                                clientIdRead8, clockRead4, 
                                                replicasWrite4, replicasWrite5, 
                                                clientsRead0, clientsWrite8, 
                                                clientsWrite9, clientsWrite10, 
                                                outsideWrite3, clockWrite3, 
                                                replicasWrite6, clientsWrite11, 
                                                outsideWrite4, spinRead0, 
                                                clockWrite4, replicasWrite7, 
                                                clientsWrite12, outsideWrite5, 
                                                clientIdRead9, clientIdRead10, 
                                                clockWrite5, replicasWrite8, 
                                                replicasWrite9, clientIdRead11, 
                                                clockRead5, clientIdRead12, 
                                                clockRead6, clientIdRead13, 
                                                clockWrite6, clientIdRead14, 
                                                clientIdRead15, clockRead7, 
                                                replicasWrite10, 
                                                replicasWrite11, clockWrite7, 
                                                replicasWrite12, spinRead1, 
                                                clockWrite8, replicasWrite13, 
                                                kvLocal, liveClients, 
                                                pendingRequests, 
                                                stableMessages, firstPending, 
                                                timestamp, lowestPending, 
                                                chooseMessage, currentClocks, 
                                                continue_, msg_, ok, key, val, 
                                                spinLocal, continue_G, getReq, 
                                                getResp, spinLocal0, 
                                                continue_P, i, j_, putReq, 
                                                putResp, msg_D, j_D, 
                                                spinLocal1, continue, j, msg >>

findMinClock(self) == /\ pc[self] = "findMinClock"
                      /\ IF (i_[self]) < (Cardinality(clientsIter[self]))
                            THEN /\ \E client \in clientsIter[self]:
                                      /\ IF ((minClock[self]) = (0)) \/ ((currentClocks[self][client]) < (minClock[self]))
                                            THEN /\ minClock' = [minClock EXCEPT ![self] = currentClocks[self][client]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED minClock
                                      /\ clientsIter' = [clientsIter EXCEPT ![self] = (clientsIter[self]) \ ({client})]
                                 /\ pc' = [pc EXCEPT ![self] = "findMinClock"]
                                 /\ UNCHANGED << i_, lowestPending >>
                            ELSE /\ lowestPending' = [lowestPending EXCEPT ![self] = (minClock[self]) + (1)]
                                 /\ i_' = [i_ EXCEPT ![self] = 0]
                                 /\ pc' = [pc EXCEPT ![self] = "findMinClient"]
                                 /\ UNCHANGED << minClock, clientsIter >>
                      /\ UNCHANGED << replicasNetwork, allClients, 
                                      clientMailboxes, cid, out, clocks, 
                                      replicasRead, replicasWrite, kvRead, 
                                      clientsWrite, clientsWrite0, kvWrite, 
                                      kvWrite0, clientsWrite1, clientsWrite2, 
                                      kvWrite1, replicasWrite0, clientsWrite3, 
                                      kvWrite2, clientIdRead, clockRead, 
                                      clientIdRead0, clockRead0, clientIdRead1, 
                                      clockWrite, keyRead, clientIdRead2, 
                                      clientIdRead3, clockRead1, 
                                      replicasWrite1, clientsRead, 
                                      clientsWrite4, outsideWrite, 
                                      clientsWrite5, outsideWrite0, 
                                      clockWrite0, replicasWrite2, 
                                      clientsWrite6, outsideWrite1, spinRead, 
                                      clockWrite1, replicasWrite3, 
                                      clientsWrite7, outsideWrite2, 
                                      clientIdRead4, clockRead2, clientIdRead5, 
                                      clockRead3, clientIdRead6, clockWrite2, 
                                      keyRead0, valueRead, clientIdRead7, 
                                      clientIdRead8, clockRead4, 
                                      replicasWrite4, replicasWrite5, 
                                      clientsRead0, clientsWrite8, 
                                      clientsWrite9, clientsWrite10, 
                                      outsideWrite3, clockWrite3, 
                                      replicasWrite6, clientsWrite11, 
                                      outsideWrite4, spinRead0, clockWrite4, 
                                      replicasWrite7, clientsWrite12, 
                                      outsideWrite5, clientIdRead9, 
                                      clientIdRead10, clockWrite5, 
                                      replicasWrite8, replicasWrite9, 
                                      clientIdRead11, clockRead5, 
                                      clientIdRead12, clockRead6, 
                                      clientIdRead13, clockWrite6, 
                                      clientIdRead14, clientIdRead15, 
                                      clockRead7, replicasWrite10, 
                                      replicasWrite11, clockWrite7, 
                                      replicasWrite12, spinRead1, clockWrite8, 
                                      replicasWrite13, kvLocal, liveClients, 
                                      pendingRequests, stableMessages, 
                                      firstPending, timestamp, nextClient, 
                                      chooseMessage, currentClocks, continue_, 
                                      pendingClients, msg_, ok, key, val, 
                                      spinLocal, continue_G, getReq, getResp, 
                                      spinLocal0, continue_P, i, j_, putReq, 
                                      putResp, msg_D, j_D, spinLocal1, 
                                      continue, j, msg >>

findMinClient(self) == /\ pc[self] = "findMinClient"
                       /\ IF (i_[self]) < (Cardinality(pendingClients[self]))
                             THEN /\ \E client \in pendingClients[self]:
                                       /\ firstPending' = [firstPending EXCEPT ![self] = Head(pendingRequests[self][client])]
                                       /\ Assert((((firstPending'[self]).op) = (GET_MSG)) \/ (((firstPending'[self]).op) = (PUT_MSG)), 
                                                 "Failure of assertion at line 722, column 37.")
                                       /\ timestamp' = [timestamp EXCEPT ![self] = (firstPending'[self]).timestamp]
                                       /\ IF (timestamp'[self]) < (minClock[self])
                                             THEN /\ chooseMessage' = [chooseMessage EXCEPT ![self] = ((timestamp'[self]) < (lowestPending[self])) \/ (((timestamp'[self]) = (lowestPending[self])) /\ ((client) < (nextClient[self])))]
                                                  /\ IF chooseMessage'[self]
                                                        THEN /\ nextClient' = [nextClient EXCEPT ![self] = client]
                                                             /\ lowestPending' = [lowestPending EXCEPT ![self] = timestamp'[self]]
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED << nextClient, 
                                                                             lowestPending >>
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << nextClient, 
                                                                  lowestPending, 
                                                                  chooseMessage >>
                                       /\ pendingClients' = [pendingClients EXCEPT ![self] = (pendingClients[self]) \ ({client})]
                                  /\ pc' = [pc EXCEPT ![self] = "findMinClient"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "addStableMessage"]
                                  /\ UNCHANGED << firstPending, timestamp, 
                                                  nextClient, lowestPending, 
                                                  chooseMessage, 
                                                  pendingClients >>
                       /\ UNCHANGED << replicasNetwork, allClients, 
                                       clientMailboxes, cid, out, clocks, 
                                       replicasRead, replicasWrite, kvRead, 
                                       clientsWrite, clientsWrite0, kvWrite, 
                                       kvWrite0, clientsWrite1, clientsWrite2, 
                                       kvWrite1, replicasWrite0, clientsWrite3, 
                                       kvWrite2, clientIdRead, clockRead, 
                                       clientIdRead0, clockRead0, 
                                       clientIdRead1, clockWrite, keyRead, 
                                       clientIdRead2, clientIdRead3, 
                                       clockRead1, replicasWrite1, clientsRead, 
                                       clientsWrite4, outsideWrite, 
                                       clientsWrite5, outsideWrite0, 
                                       clockWrite0, replicasWrite2, 
                                       clientsWrite6, outsideWrite1, spinRead, 
                                       clockWrite1, replicasWrite3, 
                                       clientsWrite7, outsideWrite2, 
                                       clientIdRead4, clockRead2, 
                                       clientIdRead5, clockRead3, 
                                       clientIdRead6, clockWrite2, keyRead0, 
                                       valueRead, clientIdRead7, clientIdRead8, 
                                       clockRead4, replicasWrite4, 
                                       replicasWrite5, clientsRead0, 
                                       clientsWrite8, clientsWrite9, 
                                       clientsWrite10, outsideWrite3, 
                                       clockWrite3, replicasWrite6, 
                                       clientsWrite11, outsideWrite4, 
                                       spinRead0, clockWrite4, replicasWrite7, 
                                       clientsWrite12, outsideWrite5, 
                                       clientIdRead9, clientIdRead10, 
                                       clockWrite5, replicasWrite8, 
                                       replicasWrite9, clientIdRead11, 
                                       clockRead5, clientIdRead12, clockRead6, 
                                       clientIdRead13, clockWrite6, 
                                       clientIdRead14, clientIdRead15, 
                                       clockRead7, replicasWrite10, 
                                       replicasWrite11, clockWrite7, 
                                       replicasWrite12, spinRead1, clockWrite8, 
                                       replicasWrite13, kvLocal, liveClients, 
                                       pendingRequests, stableMessages, i_, 
                                       currentClocks, minClock, continue_, 
                                       clientsIter, msg_, ok, key, val, 
                                       spinLocal, continue_G, getReq, getResp, 
                                       spinLocal0, continue_P, i, j_, putReq, 
                                       putResp, msg_D, j_D, spinLocal1, 
                                       continue, j, msg >>

addStableMessage(self) == /\ pc[self] = "addStableMessage"
                          /\ IF (lowestPending[self]) < (minClock[self])
                                THEN /\ msg_' = [msg_ EXCEPT ![self] = Head(pendingRequests[self][nextClient[self]])]
                                     /\ pendingRequests' = [pendingRequests EXCEPT ![self][nextClient[self]] = Tail(pendingRequests[self][nextClient[self]])]
                                     /\ stableMessages' = [stableMessages EXCEPT ![self] = Append(stableMessages[self], msg_'[self])]
                                     /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                                     /\ UNCHANGED continue_
                                ELSE /\ continue_' = [continue_ EXCEPT ![self] = FALSE]
                                     /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                                     /\ UNCHANGED << pendingRequests, 
                                                     stableMessages, msg_ >>
                          /\ UNCHANGED << replicasNetwork, allClients, 
                                          clientMailboxes, cid, out, clocks, 
                                          replicasRead, replicasWrite, kvRead, 
                                          clientsWrite, clientsWrite0, kvWrite, 
                                          kvWrite0, clientsWrite1, 
                                          clientsWrite2, kvWrite1, 
                                          replicasWrite0, clientsWrite3, 
                                          kvWrite2, clientIdRead, clockRead, 
                                          clientIdRead0, clockRead0, 
                                          clientIdRead1, clockWrite, keyRead, 
                                          clientIdRead2, clientIdRead3, 
                                          clockRead1, replicasWrite1, 
                                          clientsRead, clientsWrite4, 
                                          outsideWrite, clientsWrite5, 
                                          outsideWrite0, clockWrite0, 
                                          replicasWrite2, clientsWrite6, 
                                          outsideWrite1, spinRead, clockWrite1, 
                                          replicasWrite3, clientsWrite7, 
                                          outsideWrite2, clientIdRead4, 
                                          clockRead2, clientIdRead5, 
                                          clockRead3, clientIdRead6, 
                                          clockWrite2, keyRead0, valueRead, 
                                          clientIdRead7, clientIdRead8, 
                                          clockRead4, replicasWrite4, 
                                          replicasWrite5, clientsRead0, 
                                          clientsWrite8, clientsWrite9, 
                                          clientsWrite10, outsideWrite3, 
                                          clockWrite3, replicasWrite6, 
                                          clientsWrite11, outsideWrite4, 
                                          spinRead0, clockWrite4, 
                                          replicasWrite7, clientsWrite12, 
                                          outsideWrite5, clientIdRead9, 
                                          clientIdRead10, clockWrite5, 
                                          replicasWrite8, replicasWrite9, 
                                          clientIdRead11, clockRead5, 
                                          clientIdRead12, clockRead6, 
                                          clientIdRead13, clockWrite6, 
                                          clientIdRead14, clientIdRead15, 
                                          clockRead7, replicasWrite10, 
                                          replicasWrite11, clockWrite7, 
                                          replicasWrite12, spinRead1, 
                                          clockWrite8, replicasWrite13, 
                                          kvLocal, liveClients, i_, 
                                          firstPending, timestamp, nextClient, 
                                          lowestPending, chooseMessage, 
                                          currentClocks, minClock, 
                                          pendingClients, clientsIter, ok, key, 
                                          val, spinLocal, continue_G, getReq, 
                                          getResp, spinLocal0, continue_P, i, 
                                          j_, putReq, putResp, msg_D, j_D, 
                                          spinLocal1, continue, j, msg >>

respondPendingRequestsLoop(self) == /\ pc[self] = "respondPendingRequestsLoop"
                                    /\ IF (i_[self]) <= (Len(stableMessages[self]))
                                          THEN /\ msg_' = [msg_ EXCEPT ![self] = stableMessages[self][i_[self]]]
                                               /\ i_' = [i_ EXCEPT ![self] = (i_[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "respondStableGet"]
                                               /\ UNCHANGED << clientMailboxes, 
                                                               clientsWrite2, 
                                                               kvWrite1, 
                                                               kvLocal >>
                                          ELSE /\ clientsWrite2' = clientMailboxes
                                               /\ kvWrite1' = kvLocal[self]
                                               /\ clientMailboxes' = clientsWrite2'
                                               /\ kvLocal' = [kvLocal EXCEPT ![self] = kvWrite1']
                                               /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                               /\ UNCHANGED << i_, msg_ >>
                                    /\ UNCHANGED << replicasNetwork, 
                                                    allClients, cid, out, 
                                                    clocks, replicasRead, 
                                                    replicasWrite, kvRead, 
                                                    clientsWrite, 
                                                    clientsWrite0, kvWrite, 
                                                    kvWrite0, clientsWrite1, 
                                                    replicasWrite0, 
                                                    clientsWrite3, kvWrite2, 
                                                    clientIdRead, clockRead, 
                                                    clientIdRead0, clockRead0, 
                                                    clientIdRead1, clockWrite, 
                                                    keyRead, clientIdRead2, 
                                                    clientIdRead3, clockRead1, 
                                                    replicasWrite1, 
                                                    clientsRead, clientsWrite4, 
                                                    outsideWrite, 
                                                    clientsWrite5, 
                                                    outsideWrite0, clockWrite0, 
                                                    replicasWrite2, 
                                                    clientsWrite6, 
                                                    outsideWrite1, spinRead, 
                                                    clockWrite1, 
                                                    replicasWrite3, 
                                                    clientsWrite7, 
                                                    outsideWrite2, 
                                                    clientIdRead4, clockRead2, 
                                                    clientIdRead5, clockRead3, 
                                                    clientIdRead6, clockWrite2, 
                                                    keyRead0, valueRead, 
                                                    clientIdRead7, 
                                                    clientIdRead8, clockRead4, 
                                                    replicasWrite4, 
                                                    replicasWrite5, 
                                                    clientsRead0, 
                                                    clientsWrite8, 
                                                    clientsWrite9, 
                                                    clientsWrite10, 
                                                    outsideWrite3, clockWrite3, 
                                                    replicasWrite6, 
                                                    clientsWrite11, 
                                                    outsideWrite4, spinRead0, 
                                                    clockWrite4, 
                                                    replicasWrite7, 
                                                    clientsWrite12, 
                                                    outsideWrite5, 
                                                    clientIdRead9, 
                                                    clientIdRead10, 
                                                    clockWrite5, 
                                                    replicasWrite8, 
                                                    replicasWrite9, 
                                                    clientIdRead11, clockRead5, 
                                                    clientIdRead12, clockRead6, 
                                                    clientIdRead13, 
                                                    clockWrite6, 
                                                    clientIdRead14, 
                                                    clientIdRead15, clockRead7, 
                                                    replicasWrite10, 
                                                    replicasWrite11, 
                                                    clockWrite7, 
                                                    replicasWrite12, spinRead1, 
                                                    clockWrite8, 
                                                    replicasWrite13, 
                                                    liveClients, 
                                                    pendingRequests, 
                                                    stableMessages, 
                                                    firstPending, timestamp, 
                                                    nextClient, lowestPending, 
                                                    chooseMessage, 
                                                    currentClocks, minClock, 
                                                    continue_, pendingClients, 
                                                    clientsIter, ok, key, val, 
                                                    spinLocal, continue_G, 
                                                    getReq, getResp, 
                                                    spinLocal0, continue_P, i, 
                                                    j_, putReq, putResp, msg_D, 
                                                    j_D, spinLocal1, continue, 
                                                    j, msg >>

respondStableGet(self) == /\ pc[self] = "respondStableGet"
                          /\ IF ((msg_[self]).op) = (GET_MSG)
                                THEN /\ key' = [key EXCEPT ![self] = (msg_[self]).key]
                                     /\ kvRead' = kvLocal[self][key'[self]]
                                     /\ val' = [val EXCEPT ![self] = kvRead']
                                     /\ (Len(clientMailboxes[(msg_[self]).reply_to])) < (BUFFER_SIZE)
                                     /\ clientsWrite' = [clientMailboxes EXCEPT ![(msg_[self]).reply_to] = Append(clientMailboxes[(msg_[self]).reply_to], [type |-> GET_RESPONSE, result |-> val'[self]])]
                                     /\ clientsWrite0' = clientsWrite'
                                     /\ clientMailboxes' = clientsWrite0'
                                ELSE /\ clientsWrite0' = clientMailboxes
                                     /\ clientMailboxes' = clientsWrite0'
                                     /\ UNCHANGED << kvRead, clientsWrite, key, 
                                                     val >>
                          /\ pc' = [pc EXCEPT ![self] = "respondStablePut"]
                          /\ UNCHANGED << replicasNetwork, allClients, cid, 
                                          out, clocks, replicasRead, 
                                          replicasWrite, kvWrite, kvWrite0, 
                                          clientsWrite1, clientsWrite2, 
                                          kvWrite1, replicasWrite0, 
                                          clientsWrite3, kvWrite2, 
                                          clientIdRead, clockRead, 
                                          clientIdRead0, clockRead0, 
                                          clientIdRead1, clockWrite, keyRead, 
                                          clientIdRead2, clientIdRead3, 
                                          clockRead1, replicasWrite1, 
                                          clientsRead, clientsWrite4, 
                                          outsideWrite, clientsWrite5, 
                                          outsideWrite0, clockWrite0, 
                                          replicasWrite2, clientsWrite6, 
                                          outsideWrite1, spinRead, clockWrite1, 
                                          replicasWrite3, clientsWrite7, 
                                          outsideWrite2, clientIdRead4, 
                                          clockRead2, clientIdRead5, 
                                          clockRead3, clientIdRead6, 
                                          clockWrite2, keyRead0, valueRead, 
                                          clientIdRead7, clientIdRead8, 
                                          clockRead4, replicasWrite4, 
                                          replicasWrite5, clientsRead0, 
                                          clientsWrite8, clientsWrite9, 
                                          clientsWrite10, outsideWrite3, 
                                          clockWrite3, replicasWrite6, 
                                          clientsWrite11, outsideWrite4, 
                                          spinRead0, clockWrite4, 
                                          replicasWrite7, clientsWrite12, 
                                          outsideWrite5, clientIdRead9, 
                                          clientIdRead10, clockWrite5, 
                                          replicasWrite8, replicasWrite9, 
                                          clientIdRead11, clockRead5, 
                                          clientIdRead12, clockRead6, 
                                          clientIdRead13, clockWrite6, 
                                          clientIdRead14, clientIdRead15, 
                                          clockRead7, replicasWrite10, 
                                          replicasWrite11, clockWrite7, 
                                          replicasWrite12, spinRead1, 
                                          clockWrite8, replicasWrite13, 
                                          kvLocal, liveClients, 
                                          pendingRequests, stableMessages, i_, 
                                          firstPending, timestamp, nextClient, 
                                          lowestPending, chooseMessage, 
                                          currentClocks, minClock, continue_, 
                                          pendingClients, clientsIter, msg_, 
                                          ok, spinLocal, continue_G, getReq, 
                                          getResp, spinLocal0, continue_P, i, 
                                          j_, putReq, putResp, msg_D, j_D, 
                                          spinLocal1, continue, j, msg >>

respondStablePut(self) == /\ pc[self] = "respondStablePut"
                          /\ IF ((msg_[self]).op) = (PUT_MSG)
                                THEN /\ key' = [key EXCEPT ![self] = (msg_[self]).key]
                                     /\ val' = [val EXCEPT ![self] = (msg_[self]).value]
                                     /\ kvWrite' = [kvLocal[self] EXCEPT ![key'[self]] = val'[self]]
                                     /\ (Len(clientMailboxes[(msg_[self]).reply_to])) < (BUFFER_SIZE)
                                     /\ clientsWrite' = [clientMailboxes EXCEPT ![(msg_[self]).reply_to] = Append(clientMailboxes[(msg_[self]).reply_to], [type |-> PUT_RESPONSE, result |-> ok[self]])]
                                     /\ kvWrite0' = kvWrite'
                                     /\ clientsWrite1' = clientsWrite'
                                     /\ clientMailboxes' = clientsWrite1'
                                     /\ kvLocal' = [kvLocal EXCEPT ![self] = kvWrite0']
                                     /\ pc' = [pc EXCEPT ![self] = "respondPendingRequestsLoop"]
                                ELSE /\ kvWrite0' = kvLocal[self]
                                     /\ clientsWrite1' = clientMailboxes
                                     /\ clientMailboxes' = clientsWrite1'
                                     /\ kvLocal' = [kvLocal EXCEPT ![self] = kvWrite0']
                                     /\ pc' = [pc EXCEPT ![self] = "respondPendingRequestsLoop"]
                                     /\ UNCHANGED << clientsWrite, kvWrite, 
                                                     key, val >>
                          /\ UNCHANGED << replicasNetwork, allClients, cid, 
                                          out, clocks, replicasRead, 
                                          replicasWrite, kvRead, clientsWrite0, 
                                          clientsWrite2, kvWrite1, 
                                          replicasWrite0, clientsWrite3, 
                                          kvWrite2, clientIdRead, clockRead, 
                                          clientIdRead0, clockRead0, 
                                          clientIdRead1, clockWrite, keyRead, 
                                          clientIdRead2, clientIdRead3, 
                                          clockRead1, replicasWrite1, 
                                          clientsRead, clientsWrite4, 
                                          outsideWrite, clientsWrite5, 
                                          outsideWrite0, clockWrite0, 
                                          replicasWrite2, clientsWrite6, 
                                          outsideWrite1, spinRead, clockWrite1, 
                                          replicasWrite3, clientsWrite7, 
                                          outsideWrite2, clientIdRead4, 
                                          clockRead2, clientIdRead5, 
                                          clockRead3, clientIdRead6, 
                                          clockWrite2, keyRead0, valueRead, 
                                          clientIdRead7, clientIdRead8, 
                                          clockRead4, replicasWrite4, 
                                          replicasWrite5, clientsRead0, 
                                          clientsWrite8, clientsWrite9, 
                                          clientsWrite10, outsideWrite3, 
                                          clockWrite3, replicasWrite6, 
                                          clientsWrite11, outsideWrite4, 
                                          spinRead0, clockWrite4, 
                                          replicasWrite7, clientsWrite12, 
                                          outsideWrite5, clientIdRead9, 
                                          clientIdRead10, clockWrite5, 
                                          replicasWrite8, replicasWrite9, 
                                          clientIdRead11, clockRead5, 
                                          clientIdRead12, clockRead6, 
                                          clientIdRead13, clockWrite6, 
                                          clientIdRead14, clientIdRead15, 
                                          clockRead7, replicasWrite10, 
                                          replicasWrite11, clockWrite7, 
                                          replicasWrite12, spinRead1, 
                                          clockWrite8, replicasWrite13, 
                                          liveClients, pendingRequests, 
                                          stableMessages, i_, firstPending, 
                                          timestamp, nextClient, lowestPending, 
                                          chooseMessage, currentClocks, 
                                          minClock, continue_, pendingClients, 
                                          clientsIter, msg_, ok, spinLocal, 
                                          continue_G, getReq, getResp, 
                                          spinLocal0, continue_P, i, j_, 
                                          putReq, putResp, msg_D, j_D, 
                                          spinLocal1, continue, j, msg >>

Replica(self) == replicaLoop(self) \/ receiveClientRequest(self)
                    \/ clientDisconnected(self) \/ replicaGetRequest(self)
                    \/ replicaPutRequest(self) \/ replicaNullRequest(self)
                    \/ findStableRequestsLoop(self) \/ findMinClock(self)
                    \/ findMinClient(self) \/ addStableMessage(self)
                    \/ respondPendingRequestsLoop(self)
                    \/ respondStableGet(self) \/ respondStablePut(self)

getLoop(self) == /\ pc[self] = "getLoop"
                 /\ IF continue_G[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "getRequest"]
                            /\ UNCHANGED << replicasNetwork, clientMailboxes, 
                                            out, clocks, clockWrite1, 
                                            replicasWrite3, clientsWrite7, 
                                            outsideWrite2 >>
                       ELSE /\ clockWrite1' = clocks
                            /\ replicasWrite3' = replicasNetwork
                            /\ clientsWrite7' = clientMailboxes
                            /\ outsideWrite2' = out
                            /\ replicasNetwork' = replicasWrite3'
                            /\ clientMailboxes' = clientsWrite7'
                            /\ clocks' = clockWrite1'
                            /\ out' = outsideWrite2'
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << allClients, cid, replicasRead, replicasWrite, 
                                 kvRead, clientsWrite, clientsWrite0, kvWrite, 
                                 kvWrite0, clientsWrite1, clientsWrite2, 
                                 kvWrite1, replicasWrite0, clientsWrite3, 
                                 kvWrite2, clientIdRead, clockRead, 
                                 clientIdRead0, clockRead0, clientIdRead1, 
                                 clockWrite, keyRead, clientIdRead2, 
                                 clientIdRead3, clockRead1, replicasWrite1, 
                                 clientsRead, clientsWrite4, outsideWrite, 
                                 clientsWrite5, outsideWrite0, clockWrite0, 
                                 replicasWrite2, clientsWrite6, outsideWrite1, 
                                 spinRead, clientIdRead4, clockRead2, 
                                 clientIdRead5, clockRead3, clientIdRead6, 
                                 clockWrite2, keyRead0, valueRead, 
                                 clientIdRead7, clientIdRead8, clockRead4, 
                                 replicasWrite4, replicasWrite5, clientsRead0, 
                                 clientsWrite8, clientsWrite9, clientsWrite10, 
                                 outsideWrite3, clockWrite3, replicasWrite6, 
                                 clientsWrite11, outsideWrite4, spinRead0, 
                                 clockWrite4, replicasWrite7, clientsWrite12, 
                                 outsideWrite5, clientIdRead9, clientIdRead10, 
                                 clockWrite5, replicasWrite8, replicasWrite9, 
                                 clientIdRead11, clockRead5, clientIdRead12, 
                                 clockRead6, clientIdRead13, clockWrite6, 
                                 clientIdRead14, clientIdRead15, clockRead7, 
                                 replicasWrite10, replicasWrite11, clockWrite7, 
                                 replicasWrite12, spinRead1, clockWrite8, 
                                 replicasWrite13, kvLocal, liveClients, 
                                 pendingRequests, stableMessages, i_, 
                                 firstPending, timestamp, nextClient, 
                                 lowestPending, chooseMessage, currentClocks, 
                                 minClock, continue_, pendingClients, 
                                 clientsIter, msg_, ok, key, val, spinLocal, 
                                 continue_G, getReq, getResp, spinLocal0, 
                                 continue_P, i, j_, putReq, putResp, msg_D, 
                                 j_D, spinLocal1, continue, j, msg >>

getRequest(self) == /\ pc[self] = "getRequest"
                    /\ clientIdRead' = (self) - ((NUM_CLIENTS) * (GET_ORDER))
                    /\ clockRead' = clocks[clientIdRead']
                    /\ IF (clockRead') = (-(1))
                          THEN /\ continue_G' = [continue_G EXCEPT ![self] = FALSE]
                               /\ clockWrite0' = clocks
                               /\ replicasWrite2' = replicasNetwork
                               /\ clientsWrite6' = clientMailboxes
                               /\ outsideWrite1' = out
                               /\ replicasNetwork' = replicasWrite2'
                               /\ clientMailboxes' = clientsWrite6'
                               /\ clocks' = clockWrite0'
                               /\ out' = outsideWrite1'
                               /\ pc' = [pc EXCEPT ![self] = "getCheckSpin"]
                               /\ UNCHANGED << clientIdRead0, clockRead0, 
                                               clientIdRead1, clockWrite, 
                                               keyRead, clientIdRead2, 
                                               clientIdRead3, clockRead1, 
                                               replicasWrite1, getReq >>
                          ELSE /\ clientIdRead0' = (self) - ((NUM_CLIENTS) * (GET_ORDER))
                               /\ clockRead0' = clocks[clientIdRead0']
                               /\ clientIdRead1' = (self) - ((NUM_CLIENTS) * (GET_ORDER))
                               /\ clockWrite' = [clocks EXCEPT ![clientIdRead1'] = (clockRead0') + (1)]
                               /\ keyRead' = GET_KEY
                               /\ clientIdRead2' = (self) - ((NUM_CLIENTS) * (GET_ORDER))
                               /\ clientIdRead3' = (self) - ((NUM_CLIENTS) * (GET_ORDER))
                               /\ clockRead1' = clockWrite'[clientIdRead3']
                               /\ getReq' = [getReq EXCEPT ![self] = [op |-> GET_MSG, key |-> keyRead', client |-> clientIdRead2', timestamp |-> clockRead1', reply_to |-> self]]
                               /\ \E dst \in ReplicaSet:
                                    /\ (Len(replicasNetwork[dst])) < (BUFFER_SIZE)
                                    /\ replicasWrite1' = [replicasNetwork EXCEPT ![dst] = Append(replicasNetwork[dst], getReq'[self])]
                               /\ replicasNetwork' = replicasWrite1'
                               /\ clocks' = clockWrite'
                               /\ pc' = [pc EXCEPT ![self] = "getReply"]
                               /\ UNCHANGED << clientMailboxes, out, 
                                               clockWrite0, replicasWrite2, 
                                               clientsWrite6, outsideWrite1, 
                                               continue_G >>
                    /\ UNCHANGED << allClients, cid, replicasRead, 
                                    replicasWrite, kvRead, clientsWrite, 
                                    clientsWrite0, kvWrite, kvWrite0, 
                                    clientsWrite1, clientsWrite2, kvWrite1, 
                                    replicasWrite0, clientsWrite3, kvWrite2, 
                                    clientsRead, clientsWrite4, outsideWrite, 
                                    clientsWrite5, outsideWrite0, spinRead, 
                                    clockWrite1, replicasWrite3, clientsWrite7, 
                                    outsideWrite2, clientIdRead4, clockRead2, 
                                    clientIdRead5, clockRead3, clientIdRead6, 
                                    clockWrite2, keyRead0, valueRead, 
                                    clientIdRead7, clientIdRead8, clockRead4, 
                                    replicasWrite4, replicasWrite5, 
                                    clientsRead0, clientsWrite8, clientsWrite9, 
                                    clientsWrite10, outsideWrite3, clockWrite3, 
                                    replicasWrite6, clientsWrite11, 
                                    outsideWrite4, spinRead0, clockWrite4, 
                                    replicasWrite7, clientsWrite12, 
                                    outsideWrite5, clientIdRead9, 
                                    clientIdRead10, clockWrite5, 
                                    replicasWrite8, replicasWrite9, 
                                    clientIdRead11, clockRead5, clientIdRead12, 
                                    clockRead6, clientIdRead13, clockWrite6, 
                                    clientIdRead14, clientIdRead15, clockRead7, 
                                    replicasWrite10, replicasWrite11, 
                                    clockWrite7, replicasWrite12, spinRead1, 
                                    clockWrite8, replicasWrite13, kvLocal, 
                                    liveClients, pendingRequests, 
                                    stableMessages, i_, firstPending, 
                                    timestamp, nextClient, lowestPending, 
                                    chooseMessage, currentClocks, minClock, 
                                    continue_, pendingClients, clientsIter, 
                                    msg_, ok, key, val, spinLocal, getResp, 
                                    spinLocal0, continue_P, i, j_, putReq, 
                                    putResp, msg_D, j_D, spinLocal1, continue, 
                                    j, msg >>

getReply(self) == /\ pc[self] = "getReply"
                  /\ clientIdRead' = (self) - ((NUM_CLIENTS) * (GET_ORDER))
                  /\ clockRead' = clocks[clientIdRead']
                  /\ IF (clockRead') = (-(1))
                        THEN /\ continue_G' = [continue_G EXCEPT ![self] = FALSE]
                             /\ clientsWrite5' = clientMailboxes
                             /\ outsideWrite0' = out
                             /\ clientMailboxes' = clientsWrite5'
                             /\ out' = outsideWrite0'
                             /\ UNCHANGED << clientsRead, clientsWrite4, 
                                             outsideWrite, getResp >>
                        ELSE /\ (Len(clientMailboxes[self])) > (0)
                             /\ LET msg1 == Head(clientMailboxes[self]) IN
                                  /\ clientsWrite4' = [clientMailboxes EXCEPT ![self] = Tail(clientMailboxes[self])]
                                  /\ clientsRead' = msg1
                             /\ getResp' = [getResp EXCEPT ![self] = clientsRead']
                             /\ Assert(((getResp'[self]).type) = (GET_RESPONSE), 
                                       "Failure of assertion at line 857, column 33.")
                             /\ outsideWrite' = (getResp'[self]).result
                             /\ clientsWrite5' = clientsWrite4'
                             /\ outsideWrite0' = outsideWrite'
                             /\ clientMailboxes' = clientsWrite5'
                             /\ out' = outsideWrite0'
                             /\ UNCHANGED continue_G
                  /\ pc' = [pc EXCEPT ![self] = "getCheckSpin"]
                  /\ UNCHANGED << replicasNetwork, allClients, cid, clocks, 
                                  replicasRead, replicasWrite, kvRead, 
                                  clientsWrite, clientsWrite0, kvWrite, 
                                  kvWrite0, clientsWrite1, clientsWrite2, 
                                  kvWrite1, replicasWrite0, clientsWrite3, 
                                  kvWrite2, clientIdRead0, clockRead0, 
                                  clientIdRead1, clockWrite, keyRead, 
                                  clientIdRead2, clientIdRead3, clockRead1, 
                                  replicasWrite1, clockWrite0, replicasWrite2, 
                                  clientsWrite6, outsideWrite1, spinRead, 
                                  clockWrite1, replicasWrite3, clientsWrite7, 
                                  outsideWrite2, clientIdRead4, clockRead2, 
                                  clientIdRead5, clockRead3, clientIdRead6, 
                                  clockWrite2, keyRead0, valueRead, 
                                  clientIdRead7, clientIdRead8, clockRead4, 
                                  replicasWrite4, replicasWrite5, clientsRead0, 
                                  clientsWrite8, clientsWrite9, clientsWrite10, 
                                  outsideWrite3, clockWrite3, replicasWrite6, 
                                  clientsWrite11, outsideWrite4, spinRead0, 
                                  clockWrite4, replicasWrite7, clientsWrite12, 
                                  outsideWrite5, clientIdRead9, clientIdRead10, 
                                  clockWrite5, replicasWrite8, replicasWrite9, 
                                  clientIdRead11, clockRead5, clientIdRead12, 
                                  clockRead6, clientIdRead13, clockWrite6, 
                                  clientIdRead14, clientIdRead15, clockRead7, 
                                  replicasWrite10, replicasWrite11, 
                                  clockWrite7, replicasWrite12, spinRead1, 
                                  clockWrite8, replicasWrite13, kvLocal, 
                                  liveClients, pendingRequests, stableMessages, 
                                  i_, firstPending, timestamp, nextClient, 
                                  lowestPending, chooseMessage, currentClocks, 
                                  minClock, continue_, pendingClients, 
                                  clientsIter, msg_, ok, key, val, spinLocal, 
                                  getReq, spinLocal0, continue_P, i, j_, 
                                  putReq, putResp, msg_D, j_D, spinLocal1, 
                                  continue, j, msg >>

getCheckSpin(self) == /\ pc[self] = "getCheckSpin"
                      /\ spinRead' = spinLocal[self]
                      /\ IF ~(spinRead')
                            THEN /\ continue_G' = [continue_G EXCEPT ![self] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "getLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "getLoop"]
                                 /\ UNCHANGED continue_G
                      /\ UNCHANGED << replicasNetwork, allClients, 
                                      clientMailboxes, cid, out, clocks, 
                                      replicasRead, replicasWrite, kvRead, 
                                      clientsWrite, clientsWrite0, kvWrite, 
                                      kvWrite0, clientsWrite1, clientsWrite2, 
                                      kvWrite1, replicasWrite0, clientsWrite3, 
                                      kvWrite2, clientIdRead, clockRead, 
                                      clientIdRead0, clockRead0, clientIdRead1, 
                                      clockWrite, keyRead, clientIdRead2, 
                                      clientIdRead3, clockRead1, 
                                      replicasWrite1, clientsRead, 
                                      clientsWrite4, outsideWrite, 
                                      clientsWrite5, outsideWrite0, 
                                      clockWrite0, replicasWrite2, 
                                      clientsWrite6, outsideWrite1, 
                                      clockWrite1, replicasWrite3, 
                                      clientsWrite7, outsideWrite2, 
                                      clientIdRead4, clockRead2, clientIdRead5, 
                                      clockRead3, clientIdRead6, clockWrite2, 
                                      keyRead0, valueRead, clientIdRead7, 
                                      clientIdRead8, clockRead4, 
                                      replicasWrite4, replicasWrite5, 
                                      clientsRead0, clientsWrite8, 
                                      clientsWrite9, clientsWrite10, 
                                      outsideWrite3, clockWrite3, 
                                      replicasWrite6, clientsWrite11, 
                                      outsideWrite4, spinRead0, clockWrite4, 
                                      replicasWrite7, clientsWrite12, 
                                      outsideWrite5, clientIdRead9, 
                                      clientIdRead10, clockWrite5, 
                                      replicasWrite8, replicasWrite9, 
                                      clientIdRead11, clockRead5, 
                                      clientIdRead12, clockRead6, 
                                      clientIdRead13, clockWrite6, 
                                      clientIdRead14, clientIdRead15, 
                                      clockRead7, replicasWrite10, 
                                      replicasWrite11, clockWrite7, 
                                      replicasWrite12, spinRead1, clockWrite8, 
                                      replicasWrite13, kvLocal, liveClients, 
                                      pendingRequests, stableMessages, i_, 
                                      firstPending, timestamp, nextClient, 
                                      lowestPending, chooseMessage, 
                                      currentClocks, minClock, continue_, 
                                      pendingClients, clientsIter, msg_, ok, 
                                      key, val, spinLocal, getReq, getResp, 
                                      spinLocal0, continue_P, i, j_, putReq, 
                                      putResp, msg_D, j_D, spinLocal1, 
                                      continue, j, msg >>

GetClient(self) == getLoop(self) \/ getRequest(self) \/ getReply(self)
                      \/ getCheckSpin(self)

putLoop(self) == /\ pc[self] = "putLoop"
                 /\ IF continue_P[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "putRequest"]
                            /\ UNCHANGED << replicasNetwork, clientMailboxes, 
                                            out, clocks, clockWrite4, 
                                            replicasWrite7, clientsWrite12, 
                                            outsideWrite5 >>
                       ELSE /\ clockWrite4' = clocks
                            /\ replicasWrite7' = replicasNetwork
                            /\ clientsWrite12' = clientMailboxes
                            /\ outsideWrite5' = out
                            /\ replicasNetwork' = replicasWrite7'
                            /\ clientMailboxes' = clientsWrite12'
                            /\ clocks' = clockWrite4'
                            /\ out' = outsideWrite5'
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << allClients, cid, replicasRead, replicasWrite, 
                                 kvRead, clientsWrite, clientsWrite0, kvWrite, 
                                 kvWrite0, clientsWrite1, clientsWrite2, 
                                 kvWrite1, replicasWrite0, clientsWrite3, 
                                 kvWrite2, clientIdRead, clockRead, 
                                 clientIdRead0, clockRead0, clientIdRead1, 
                                 clockWrite, keyRead, clientIdRead2, 
                                 clientIdRead3, clockRead1, replicasWrite1, 
                                 clientsRead, clientsWrite4, outsideWrite, 
                                 clientsWrite5, outsideWrite0, clockWrite0, 
                                 replicasWrite2, clientsWrite6, outsideWrite1, 
                                 spinRead, clockWrite1, replicasWrite3, 
                                 clientsWrite7, outsideWrite2, clientIdRead4, 
                                 clockRead2, clientIdRead5, clockRead3, 
                                 clientIdRead6, clockWrite2, keyRead0, 
                                 valueRead, clientIdRead7, clientIdRead8, 
                                 clockRead4, replicasWrite4, replicasWrite5, 
                                 clientsRead0, clientsWrite8, clientsWrite9, 
                                 clientsWrite10, outsideWrite3, clockWrite3, 
                                 replicasWrite6, clientsWrite11, outsideWrite4, 
                                 spinRead0, clientIdRead9, clientIdRead10, 
                                 clockWrite5, replicasWrite8, replicasWrite9, 
                                 clientIdRead11, clockRead5, clientIdRead12, 
                                 clockRead6, clientIdRead13, clockWrite6, 
                                 clientIdRead14, clientIdRead15, clockRead7, 
                                 replicasWrite10, replicasWrite11, clockWrite7, 
                                 replicasWrite12, spinRead1, clockWrite8, 
                                 replicasWrite13, kvLocal, liveClients, 
                                 pendingRequests, stableMessages, i_, 
                                 firstPending, timestamp, nextClient, 
                                 lowestPending, chooseMessage, currentClocks, 
                                 minClock, continue_, pendingClients, 
                                 clientsIter, msg_, ok, key, val, spinLocal, 
                                 continue_G, getReq, getResp, spinLocal0, 
                                 continue_P, i, j_, putReq, putResp, msg_D, 
                                 j_D, spinLocal1, continue, j, msg >>

putRequest(self) == /\ pc[self] = "putRequest"
                    /\ clientIdRead4' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                    /\ clockRead2' = clocks[clientIdRead4']
                    /\ IF (clockRead2') = (-(1))
                          THEN /\ continue_P' = [continue_P EXCEPT ![self] = FALSE]
                               /\ clockWrite3' = clocks
                               /\ replicasWrite6' = replicasNetwork
                               /\ clientsWrite11' = clientMailboxes
                               /\ outsideWrite4' = out
                               /\ replicasNetwork' = replicasWrite6'
                               /\ clientMailboxes' = clientsWrite11'
                               /\ clocks' = clockWrite3'
                               /\ out' = outsideWrite4'
                               /\ pc' = [pc EXCEPT ![self] = "putCheckSpin"]
                               /\ UNCHANGED << clientIdRead5, clockRead3, 
                                               clientIdRead6, clockWrite2, 
                                               keyRead0, valueRead, 
                                               clientIdRead7, clientIdRead8, 
                                               clockRead4, i, j_, putReq >>
                          ELSE /\ clientIdRead5' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                               /\ clockRead3' = clocks[clientIdRead5']
                               /\ clientIdRead6' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                               /\ clockWrite2' = [clocks EXCEPT ![clientIdRead6'] = (clockRead3') + (1)]
                               /\ keyRead0' = PUT_KEY
                               /\ valueRead' = PUT_VALUE
                               /\ clientIdRead7' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                               /\ clientIdRead8' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                               /\ clockRead4' = clockWrite2'[clientIdRead8']
                               /\ putReq' = [putReq EXCEPT ![self] = [op |-> PUT_MSG, key |-> keyRead0', value |-> valueRead', client |-> clientIdRead7', timestamp |-> clockRead4', reply_to |-> self]]
                               /\ i' = [i EXCEPT ![self] = 0]
                               /\ j_' = [j_ EXCEPT ![self] = 0]
                               /\ clocks' = clockWrite2'
                               /\ pc' = [pc EXCEPT ![self] = "putBroadcast"]
                               /\ UNCHANGED << replicasNetwork, 
                                               clientMailboxes, out, 
                                               clockWrite3, replicasWrite6, 
                                               clientsWrite11, outsideWrite4, 
                                               continue_P >>
                    /\ UNCHANGED << allClients, cid, replicasRead, 
                                    replicasWrite, kvRead, clientsWrite, 
                                    clientsWrite0, kvWrite, kvWrite0, 
                                    clientsWrite1, clientsWrite2, kvWrite1, 
                                    replicasWrite0, clientsWrite3, kvWrite2, 
                                    clientIdRead, clockRead, clientIdRead0, 
                                    clockRead0, clientIdRead1, clockWrite, 
                                    keyRead, clientIdRead2, clientIdRead3, 
                                    clockRead1, replicasWrite1, clientsRead, 
                                    clientsWrite4, outsideWrite, clientsWrite5, 
                                    outsideWrite0, clockWrite0, replicasWrite2, 
                                    clientsWrite6, outsideWrite1, spinRead, 
                                    clockWrite1, replicasWrite3, clientsWrite7, 
                                    outsideWrite2, replicasWrite4, 
                                    replicasWrite5, clientsRead0, 
                                    clientsWrite8, clientsWrite9, 
                                    clientsWrite10, outsideWrite3, spinRead0, 
                                    clockWrite4, replicasWrite7, 
                                    clientsWrite12, outsideWrite5, 
                                    clientIdRead9, clientIdRead10, clockWrite5, 
                                    replicasWrite8, replicasWrite9, 
                                    clientIdRead11, clockRead5, clientIdRead12, 
                                    clockRead6, clientIdRead13, clockWrite6, 
                                    clientIdRead14, clientIdRead15, clockRead7, 
                                    replicasWrite10, replicasWrite11, 
                                    clockWrite7, replicasWrite12, spinRead1, 
                                    clockWrite8, replicasWrite13, kvLocal, 
                                    liveClients, pendingRequests, 
                                    stableMessages, i_, firstPending, 
                                    timestamp, nextClient, lowestPending, 
                                    chooseMessage, currentClocks, minClock, 
                                    continue_, pendingClients, clientsIter, 
                                    msg_, ok, key, val, spinLocal, continue_G, 
                                    getReq, getResp, spinLocal0, putResp, 
                                    msg_D, j_D, spinLocal1, continue, j, msg >>

putBroadcast(self) == /\ pc[self] = "putBroadcast"
                      /\ clientIdRead4' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                      /\ clockRead2' = clocks[clientIdRead4']
                      /\ IF ((j_[self]) <= ((NUM_REPLICAS) - (1))) /\ ((clockRead2') # (-(1)))
                            THEN /\ (Len(replicasNetwork[j_[self]])) < (BUFFER_SIZE)
                                 /\ replicasWrite4' = [replicasNetwork EXCEPT ![j_[self]] = Append(replicasNetwork[j_[self]], putReq[self])]
                                 /\ j_' = [j_ EXCEPT ![self] = (j_[self]) + (1)]
                                 /\ replicasWrite5' = replicasWrite4'
                                 /\ replicasNetwork' = replicasWrite5'
                                 /\ pc' = [pc EXCEPT ![self] = "putBroadcast"]
                            ELSE /\ replicasWrite5' = replicasNetwork
                                 /\ replicasNetwork' = replicasWrite5'
                                 /\ pc' = [pc EXCEPT ![self] = "putResponse"]
                                 /\ UNCHANGED << replicasWrite4, j_ >>
                      /\ UNCHANGED << allClients, clientMailboxes, cid, out, 
                                      clocks, replicasRead, replicasWrite, 
                                      kvRead, clientsWrite, clientsWrite0, 
                                      kvWrite, kvWrite0, clientsWrite1, 
                                      clientsWrite2, kvWrite1, replicasWrite0, 
                                      clientsWrite3, kvWrite2, clientIdRead, 
                                      clockRead, clientIdRead0, clockRead0, 
                                      clientIdRead1, clockWrite, keyRead, 
                                      clientIdRead2, clientIdRead3, clockRead1, 
                                      replicasWrite1, clientsRead, 
                                      clientsWrite4, outsideWrite, 
                                      clientsWrite5, outsideWrite0, 
                                      clockWrite0, replicasWrite2, 
                                      clientsWrite6, outsideWrite1, spinRead, 
                                      clockWrite1, replicasWrite3, 
                                      clientsWrite7, outsideWrite2, 
                                      clientIdRead5, clockRead3, clientIdRead6, 
                                      clockWrite2, keyRead0, valueRead, 
                                      clientIdRead7, clientIdRead8, clockRead4, 
                                      clientsRead0, clientsWrite8, 
                                      clientsWrite9, clientsWrite10, 
                                      outsideWrite3, clockWrite3, 
                                      replicasWrite6, clientsWrite11, 
                                      outsideWrite4, spinRead0, clockWrite4, 
                                      replicasWrite7, clientsWrite12, 
                                      outsideWrite5, clientIdRead9, 
                                      clientIdRead10, clockWrite5, 
                                      replicasWrite8, replicasWrite9, 
                                      clientIdRead11, clockRead5, 
                                      clientIdRead12, clockRead6, 
                                      clientIdRead13, clockWrite6, 
                                      clientIdRead14, clientIdRead15, 
                                      clockRead7, replicasWrite10, 
                                      replicasWrite11, clockWrite7, 
                                      replicasWrite12, spinRead1, clockWrite8, 
                                      replicasWrite13, kvLocal, liveClients, 
                                      pendingRequests, stableMessages, i_, 
                                      firstPending, timestamp, nextClient, 
                                      lowestPending, chooseMessage, 
                                      currentClocks, minClock, continue_, 
                                      pendingClients, clientsIter, msg_, ok, 
                                      key, val, spinLocal, continue_G, getReq, 
                                      getResp, spinLocal0, continue_P, i, 
                                      putReq, putResp, msg_D, j_D, spinLocal1, 
                                      continue, j, msg >>

putResponse(self) == /\ pc[self] = "putResponse"
                     /\ IF (i[self]) < (Cardinality(ReplicaSet))
                           THEN /\ clientIdRead4' = (self) - ((NUM_CLIENTS) * (PUT_ORDER))
                                /\ clockRead2' = clocks[clientIdRead4']
                                /\ IF (clockRead2') = (-(1))
                                      THEN /\ continue_P' = [continue_P EXCEPT ![self] = FALSE]
                                           /\ clientsWrite9' = clientMailboxes
                                           /\ clientsWrite10' = clientsWrite9'
                                           /\ clientMailboxes' = clientsWrite10'
                                           /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                                           /\ UNCHANGED << clientsRead0, 
                                                           clientsWrite8, i, 
                                                           putResp >>
                                      ELSE /\ (Len(clientMailboxes[self])) > (0)
                                           /\ LET msg2 == Head(clientMailboxes[self]) IN
                                                /\ clientsWrite8' = [clientMailboxes EXCEPT ![self] = Tail(clientMailboxes[self])]
                                                /\ clientsRead0' = msg2
                                           /\ putResp' = [putResp EXCEPT ![self] = clientsRead0']
                                           /\ Assert(((putResp'[self]).type) = (PUT_RESPONSE), 
                                                     "Failure of assertion at line 952, column 37.")
                                           /\ i' = [i EXCEPT ![self] = (i[self]) + (1)]
                                           /\ clientsWrite9' = clientsWrite8'
                                           /\ clientsWrite10' = clientsWrite9'
                                           /\ clientMailboxes' = clientsWrite10'
                                           /\ pc' = [pc EXCEPT ![self] = "putResponse"]
                                           /\ UNCHANGED continue_P
                           ELSE /\ clientsWrite10' = clientMailboxes
                                /\ clientMailboxes' = clientsWrite10'
                                /\ pc' = [pc EXCEPT ![self] = "putComplete"]
                                /\ UNCHANGED << clientIdRead4, clockRead2, 
                                                clientsRead0, clientsWrite8, 
                                                clientsWrite9, continue_P, i, 
                                                putResp >>
                     /\ UNCHANGED << replicasNetwork, allClients, cid, out, 
                                     clocks, replicasRead, replicasWrite, 
                                     kvRead, clientsWrite, clientsWrite0, 
                                     kvWrite, kvWrite0, clientsWrite1, 
                                     clientsWrite2, kvWrite1, replicasWrite0, 
                                     clientsWrite3, kvWrite2, clientIdRead, 
                                     clockRead, clientIdRead0, clockRead0, 
                                     clientIdRead1, clockWrite, keyRead, 
                                     clientIdRead2, clientIdRead3, clockRead1, 
                                     replicasWrite1, clientsRead, 
                                     clientsWrite4, outsideWrite, 
                                     clientsWrite5, outsideWrite0, clockWrite0, 
                                     replicasWrite2, clientsWrite6, 
                                     outsideWrite1, spinRead, clockWrite1, 
                                     replicasWrite3, clientsWrite7, 
                                     outsideWrite2, clientIdRead5, clockRead3, 
                                     clientIdRead6, clockWrite2, keyRead0, 
                                     valueRead, clientIdRead7, clientIdRead8, 
                                     clockRead4, replicasWrite4, 
                                     replicasWrite5, outsideWrite3, 
                                     clockWrite3, replicasWrite6, 
                                     clientsWrite11, outsideWrite4, spinRead0, 
                                     clockWrite4, replicasWrite7, 
                                     clientsWrite12, outsideWrite5, 
                                     clientIdRead9, clientIdRead10, 
                                     clockWrite5, replicasWrite8, 
                                     replicasWrite9, clientIdRead11, 
                                     clockRead5, clientIdRead12, clockRead6, 
                                     clientIdRead13, clockWrite6, 
                                     clientIdRead14, clientIdRead15, 
                                     clockRead7, replicasWrite10, 
                                     replicasWrite11, clockWrite7, 
                                     replicasWrite12, spinRead1, clockWrite8, 
                                     replicasWrite13, kvLocal, liveClients, 
                                     pendingRequests, stableMessages, i_, 
                                     firstPending, timestamp, nextClient, 
                                     lowestPending, chooseMessage, 
                                     currentClocks, minClock, continue_, 
                                     pendingClients, clientsIter, msg_, ok, 
                                     key, val, spinLocal, continue_G, getReq, 
                                     getResp, spinLocal0, j_, putReq, msg_D, 
                                     j_D, spinLocal1, continue, j, msg >>

putComplete(self) == /\ pc[self] = "putComplete"
                     /\ outsideWrite3' = PUT_RESPONSE
                     /\ out' = outsideWrite3'
                     /\ pc' = [pc EXCEPT ![self] = "putCheckSpin"]
                     /\ UNCHANGED << replicasNetwork, allClients, 
                                     clientMailboxes, cid, clocks, 
                                     replicasRead, replicasWrite, kvRead, 
                                     clientsWrite, clientsWrite0, kvWrite, 
                                     kvWrite0, clientsWrite1, clientsWrite2, 
                                     kvWrite1, replicasWrite0, clientsWrite3, 
                                     kvWrite2, clientIdRead, clockRead, 
                                     clientIdRead0, clockRead0, clientIdRead1, 
                                     clockWrite, keyRead, clientIdRead2, 
                                     clientIdRead3, clockRead1, replicasWrite1, 
                                     clientsRead, clientsWrite4, outsideWrite, 
                                     clientsWrite5, outsideWrite0, clockWrite0, 
                                     replicasWrite2, clientsWrite6, 
                                     outsideWrite1, spinRead, clockWrite1, 
                                     replicasWrite3, clientsWrite7, 
                                     outsideWrite2, clientIdRead4, clockRead2, 
                                     clientIdRead5, clockRead3, clientIdRead6, 
                                     clockWrite2, keyRead0, valueRead, 
                                     clientIdRead7, clientIdRead8, clockRead4, 
                                     replicasWrite4, replicasWrite5, 
                                     clientsRead0, clientsWrite8, 
                                     clientsWrite9, clientsWrite10, 
                                     clockWrite3, replicasWrite6, 
                                     clientsWrite11, outsideWrite4, spinRead0, 
                                     clockWrite4, replicasWrite7, 
                                     clientsWrite12, outsideWrite5, 
                                     clientIdRead9, clientIdRead10, 
                                     clockWrite5, replicasWrite8, 
                                     replicasWrite9, clientIdRead11, 
                                     clockRead5, clientIdRead12, clockRead6, 
                                     clientIdRead13, clockWrite6, 
                                     clientIdRead14, clientIdRead15, 
                                     clockRead7, replicasWrite10, 
                                     replicasWrite11, clockWrite7, 
                                     replicasWrite12, spinRead1, clockWrite8, 
                                     replicasWrite13, kvLocal, liveClients, 
                                     pendingRequests, stableMessages, i_, 
                                     firstPending, timestamp, nextClient, 
                                     lowestPending, chooseMessage, 
                                     currentClocks, minClock, continue_, 
                                     pendingClients, clientsIter, msg_, ok, 
                                     key, val, spinLocal, continue_G, getReq, 
                                     getResp, spinLocal0, continue_P, i, j_, 
                                     putReq, putResp, msg_D, j_D, spinLocal1, 
                                     continue, j, msg >>

putCheckSpin(self) == /\ pc[self] = "putCheckSpin"
                      /\ spinRead0' = spinLocal0[self]
                      /\ IF ~(spinRead0')
                            THEN /\ continue_P' = [continue_P EXCEPT ![self] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                                 /\ UNCHANGED continue_P
                      /\ UNCHANGED << replicasNetwork, allClients, 
                                      clientMailboxes, cid, out, clocks, 
                                      replicasRead, replicasWrite, kvRead, 
                                      clientsWrite, clientsWrite0, kvWrite, 
                                      kvWrite0, clientsWrite1, clientsWrite2, 
                                      kvWrite1, replicasWrite0, clientsWrite3, 
                                      kvWrite2, clientIdRead, clockRead, 
                                      clientIdRead0, clockRead0, clientIdRead1, 
                                      clockWrite, keyRead, clientIdRead2, 
                                      clientIdRead3, clockRead1, 
                                      replicasWrite1, clientsRead, 
                                      clientsWrite4, outsideWrite, 
                                      clientsWrite5, outsideWrite0, 
                                      clockWrite0, replicasWrite2, 
                                      clientsWrite6, outsideWrite1, spinRead, 
                                      clockWrite1, replicasWrite3, 
                                      clientsWrite7, outsideWrite2, 
                                      clientIdRead4, clockRead2, clientIdRead5, 
                                      clockRead3, clientIdRead6, clockWrite2, 
                                      keyRead0, valueRead, clientIdRead7, 
                                      clientIdRead8, clockRead4, 
                                      replicasWrite4, replicasWrite5, 
                                      clientsRead0, clientsWrite8, 
                                      clientsWrite9, clientsWrite10, 
                                      outsideWrite3, clockWrite3, 
                                      replicasWrite6, clientsWrite11, 
                                      outsideWrite4, clockWrite4, 
                                      replicasWrite7, clientsWrite12, 
                                      outsideWrite5, clientIdRead9, 
                                      clientIdRead10, clockWrite5, 
                                      replicasWrite8, replicasWrite9, 
                                      clientIdRead11, clockRead5, 
                                      clientIdRead12, clockRead6, 
                                      clientIdRead13, clockWrite6, 
                                      clientIdRead14, clientIdRead15, 
                                      clockRead7, replicasWrite10, 
                                      replicasWrite11, clockWrite7, 
                                      replicasWrite12, spinRead1, clockWrite8, 
                                      replicasWrite13, kvLocal, liveClients, 
                                      pendingRequests, stableMessages, i_, 
                                      firstPending, timestamp, nextClient, 
                                      lowestPending, chooseMessage, 
                                      currentClocks, minClock, continue_, 
                                      pendingClients, clientsIter, msg_, ok, 
                                      key, val, spinLocal, continue_G, getReq, 
                                      getResp, spinLocal0, i, j_, putReq, 
                                      putResp, msg_D, j_D, spinLocal1, 
                                      continue, j, msg >>

PutClient(self) == putLoop(self) \/ putRequest(self) \/ putBroadcast(self)
                      \/ putResponse(self) \/ putComplete(self)
                      \/ putCheckSpin(self)

sendDisconnectRequest(self) == /\ pc[self] = "sendDisconnectRequest"
                               /\ clientIdRead9' = (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER))
                               /\ msg_D' = [msg_D EXCEPT ![self] = [op |-> DISCONNECT_MSG, client |-> clientIdRead9']]
                               /\ clientIdRead10' = (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER))
                               /\ clockWrite5' = [clocks EXCEPT ![clientIdRead10'] = -(1)]
                               /\ j_D' = [j_D EXCEPT ![self] = 0]
                               /\ clocks' = clockWrite5'
                               /\ pc' = [pc EXCEPT ![self] = "disconnectBroadcast"]
                               /\ UNCHANGED << replicasNetwork, allClients, 
                                               clientMailboxes, cid, out, 
                                               replicasRead, replicasWrite, 
                                               kvRead, clientsWrite, 
                                               clientsWrite0, kvWrite, 
                                               kvWrite0, clientsWrite1, 
                                               clientsWrite2, kvWrite1, 
                                               replicasWrite0, clientsWrite3, 
                                               kvWrite2, clientIdRead, 
                                               clockRead, clientIdRead0, 
                                               clockRead0, clientIdRead1, 
                                               clockWrite, keyRead, 
                                               clientIdRead2, clientIdRead3, 
                                               clockRead1, replicasWrite1, 
                                               clientsRead, clientsWrite4, 
                                               outsideWrite, clientsWrite5, 
                                               outsideWrite0, clockWrite0, 
                                               replicasWrite2, clientsWrite6, 
                                               outsideWrite1, spinRead, 
                                               clockWrite1, replicasWrite3, 
                                               clientsWrite7, outsideWrite2, 
                                               clientIdRead4, clockRead2, 
                                               clientIdRead5, clockRead3, 
                                               clientIdRead6, clockWrite2, 
                                               keyRead0, valueRead, 
                                               clientIdRead7, clientIdRead8, 
                                               clockRead4, replicasWrite4, 
                                               replicasWrite5, clientsRead0, 
                                               clientsWrite8, clientsWrite9, 
                                               clientsWrite10, outsideWrite3, 
                                               clockWrite3, replicasWrite6, 
                                               clientsWrite11, outsideWrite4, 
                                               spinRead0, clockWrite4, 
                                               replicasWrite7, clientsWrite12, 
                                               outsideWrite5, replicasWrite8, 
                                               replicasWrite9, clientIdRead11, 
                                               clockRead5, clientIdRead12, 
                                               clockRead6, clientIdRead13, 
                                               clockWrite6, clientIdRead14, 
                                               clientIdRead15, clockRead7, 
                                               replicasWrite10, 
                                               replicasWrite11, clockWrite7, 
                                               replicasWrite12, spinRead1, 
                                               clockWrite8, replicasWrite13, 
                                               kvLocal, liveClients, 
                                               pendingRequests, stableMessages, 
                                               i_, firstPending, timestamp, 
                                               nextClient, lowestPending, 
                                               chooseMessage, currentClocks, 
                                               minClock, continue_, 
                                               pendingClients, clientsIter, 
                                               msg_, ok, key, val, spinLocal, 
                                               continue_G, getReq, getResp, 
                                               spinLocal0, continue_P, i, j_, 
                                               putReq, putResp, spinLocal1, 
                                               continue, j, msg >>

disconnectBroadcast(self) == /\ pc[self] = "disconnectBroadcast"
                             /\ IF ((j_D[self]) <= ((NUM_REPLICAS) - (1))) /\ ((0) # (-(1)))
                                   THEN /\ (Len(replicasNetwork[j_D[self]])) < (BUFFER_SIZE)
                                        /\ replicasWrite8' = [replicasNetwork EXCEPT ![j_D[self]] = Append(replicasNetwork[j_D[self]], msg_D[self])]
                                        /\ j_D' = [j_D EXCEPT ![self] = (j_D[self]) + (1)]
                                        /\ replicasWrite9' = replicasWrite8'
                                        /\ replicasNetwork' = replicasWrite9'
                                        /\ pc' = [pc EXCEPT ![self] = "disconnectBroadcast"]
                                   ELSE /\ replicasWrite9' = replicasNetwork
                                        /\ replicasNetwork' = replicasWrite9'
                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED << replicasWrite8, j_D >>
                             /\ UNCHANGED << allClients, clientMailboxes, cid, 
                                             out, clocks, replicasRead, 
                                             replicasWrite, kvRead, 
                                             clientsWrite, clientsWrite0, 
                                             kvWrite, kvWrite0, clientsWrite1, 
                                             clientsWrite2, kvWrite1, 
                                             replicasWrite0, clientsWrite3, 
                                             kvWrite2, clientIdRead, clockRead, 
                                             clientIdRead0, clockRead0, 
                                             clientIdRead1, clockWrite, 
                                             keyRead, clientIdRead2, 
                                             clientIdRead3, clockRead1, 
                                             replicasWrite1, clientsRead, 
                                             clientsWrite4, outsideWrite, 
                                             clientsWrite5, outsideWrite0, 
                                             clockWrite0, replicasWrite2, 
                                             clientsWrite6, outsideWrite1, 
                                             spinRead, clockWrite1, 
                                             replicasWrite3, clientsWrite7, 
                                             outsideWrite2, clientIdRead4, 
                                             clockRead2, clientIdRead5, 
                                             clockRead3, clientIdRead6, 
                                             clockWrite2, keyRead0, valueRead, 
                                             clientIdRead7, clientIdRead8, 
                                             clockRead4, replicasWrite4, 
                                             replicasWrite5, clientsRead0, 
                                             clientsWrite8, clientsWrite9, 
                                             clientsWrite10, outsideWrite3, 
                                             clockWrite3, replicasWrite6, 
                                             clientsWrite11, outsideWrite4, 
                                             spinRead0, clockWrite4, 
                                             replicasWrite7, clientsWrite12, 
                                             outsideWrite5, clientIdRead9, 
                                             clientIdRead10, clockWrite5, 
                                             clientIdRead11, clockRead5, 
                                             clientIdRead12, clockRead6, 
                                             clientIdRead13, clockWrite6, 
                                             clientIdRead14, clientIdRead15, 
                                             clockRead7, replicasWrite10, 
                                             replicasWrite11, clockWrite7, 
                                             replicasWrite12, spinRead1, 
                                             clockWrite8, replicasWrite13, 
                                             kvLocal, liveClients, 
                                             pendingRequests, stableMessages, 
                                             i_, firstPending, timestamp, 
                                             nextClient, lowestPending, 
                                             chooseMessage, currentClocks, 
                                             minClock, continue_, 
                                             pendingClients, clientsIter, msg_, 
                                             ok, key, val, spinLocal, 
                                             continue_G, getReq, getResp, 
                                             spinLocal0, continue_P, i, j_, 
                                             putReq, putResp, msg_D, 
                                             spinLocal1, continue, j, msg >>

DisconnectClient(self) == sendDisconnectRequest(self)
                             \/ disconnectBroadcast(self)

clockUpdateLoop(self) == /\ pc[self] = "clockUpdateLoop"
                         /\ IF continue[self]
                               THEN /\ clientIdRead11' = (self) - ((NUM_CLIENTS) * (NULL_ORDER))
                                    /\ clockRead5' = clocks[clientIdRead11']
                                    /\ IF (clockRead5') = (-(1))
                                          THEN /\ continue' = [continue EXCEPT ![self] = FALSE]
                                               /\ clockWrite7' = clocks
                                               /\ replicasWrite12' = replicasNetwork
                                               /\ replicasNetwork' = replicasWrite12'
                                               /\ clocks' = clockWrite7'
                                               /\ pc' = [pc EXCEPT ![self] = "nullCheckSpin"]
                                               /\ UNCHANGED << clientIdRead12, 
                                                               clockRead6, 
                                                               clientIdRead13, 
                                                               clockWrite6, 
                                                               clientIdRead14, 
                                                               clientIdRead15, 
                                                               clockRead7, j, 
                                                               msg >>
                                          ELSE /\ clientIdRead12' = (self) - ((NUM_CLIENTS) * (NULL_ORDER))
                                               /\ clockRead6' = clocks[clientIdRead12']
                                               /\ clientIdRead13' = (self) - ((NUM_CLIENTS) * (NULL_ORDER))
                                               /\ clockWrite6' = [clocks EXCEPT ![clientIdRead13'] = (clockRead6') + (1)]
                                               /\ clientIdRead14' = (self) - ((NUM_CLIENTS) * (NULL_ORDER))
                                               /\ clientIdRead15' = (self) - ((NUM_CLIENTS) * (NULL_ORDER))
                                               /\ clockRead7' = clockWrite6'[clientIdRead15']
                                               /\ msg' = [msg EXCEPT ![self] = [op |-> NULL_MSG, client |-> clientIdRead14', timestamp |-> clockRead7']]
                                               /\ j' = [j EXCEPT ![self] = 0]
                                               /\ clocks' = clockWrite6'
                                               /\ pc' = [pc EXCEPT ![self] = "nullBroadcast"]
                                               /\ UNCHANGED << replicasNetwork, 
                                                               clockWrite7, 
                                                               replicasWrite12, 
                                                               continue >>
                                    /\ UNCHANGED << clockWrite8, 
                                                    replicasWrite13 >>
                               ELSE /\ clockWrite8' = clocks
                                    /\ replicasWrite13' = replicasNetwork
                                    /\ replicasNetwork' = replicasWrite13'
                                    /\ clocks' = clockWrite8'
                                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << clientIdRead11, clockRead5, 
                                                    clientIdRead12, clockRead6, 
                                                    clientIdRead13, 
                                                    clockWrite6, 
                                                    clientIdRead14, 
                                                    clientIdRead15, clockRead7, 
                                                    clockWrite7, 
                                                    replicasWrite12, continue, 
                                                    j, msg >>
                         /\ UNCHANGED << allClients, clientMailboxes, cid, out, 
                                         replicasRead, replicasWrite, kvRead, 
                                         clientsWrite, clientsWrite0, kvWrite, 
                                         kvWrite0, clientsWrite1, 
                                         clientsWrite2, kvWrite1, 
                                         replicasWrite0, clientsWrite3, 
                                         kvWrite2, clientIdRead, clockRead, 
                                         clientIdRead0, clockRead0, 
                                         clientIdRead1, clockWrite, keyRead, 
                                         clientIdRead2, clientIdRead3, 
                                         clockRead1, replicasWrite1, 
                                         clientsRead, clientsWrite4, 
                                         outsideWrite, clientsWrite5, 
                                         outsideWrite0, clockWrite0, 
                                         replicasWrite2, clientsWrite6, 
                                         outsideWrite1, spinRead, clockWrite1, 
                                         replicasWrite3, clientsWrite7, 
                                         outsideWrite2, clientIdRead4, 
                                         clockRead2, clientIdRead5, clockRead3, 
                                         clientIdRead6, clockWrite2, keyRead0, 
                                         valueRead, clientIdRead7, 
                                         clientIdRead8, clockRead4, 
                                         replicasWrite4, replicasWrite5, 
                                         clientsRead0, clientsWrite8, 
                                         clientsWrite9, clientsWrite10, 
                                         outsideWrite3, clockWrite3, 
                                         replicasWrite6, clientsWrite11, 
                                         outsideWrite4, spinRead0, clockWrite4, 
                                         replicasWrite7, clientsWrite12, 
                                         outsideWrite5, clientIdRead9, 
                                         clientIdRead10, clockWrite5, 
                                         replicasWrite8, replicasWrite9, 
                                         replicasWrite10, replicasWrite11, 
                                         spinRead1, kvLocal, liveClients, 
                                         pendingRequests, stableMessages, i_, 
                                         firstPending, timestamp, nextClient, 
                                         lowestPending, chooseMessage, 
                                         currentClocks, minClock, continue_, 
                                         pendingClients, clientsIter, msg_, ok, 
                                         key, val, spinLocal, continue_G, 
                                         getReq, getResp, spinLocal0, 
                                         continue_P, i, j_, putReq, putResp, 
                                         msg_D, j_D, spinLocal1 >>

nullCheckSpin(self) == /\ pc[self] = "nullCheckSpin"
                       /\ spinRead1' = spinLocal1[self]
                       /\ IF ~(spinRead1')
                             THEN /\ continue' = [continue EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "clockUpdateLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "clockUpdateLoop"]
                                  /\ UNCHANGED continue
                       /\ UNCHANGED << replicasNetwork, allClients, 
                                       clientMailboxes, cid, out, clocks, 
                                       replicasRead, replicasWrite, kvRead, 
                                       clientsWrite, clientsWrite0, kvWrite, 
                                       kvWrite0, clientsWrite1, clientsWrite2, 
                                       kvWrite1, replicasWrite0, clientsWrite3, 
                                       kvWrite2, clientIdRead, clockRead, 
                                       clientIdRead0, clockRead0, 
                                       clientIdRead1, clockWrite, keyRead, 
                                       clientIdRead2, clientIdRead3, 
                                       clockRead1, replicasWrite1, clientsRead, 
                                       clientsWrite4, outsideWrite, 
                                       clientsWrite5, outsideWrite0, 
                                       clockWrite0, replicasWrite2, 
                                       clientsWrite6, outsideWrite1, spinRead, 
                                       clockWrite1, replicasWrite3, 
                                       clientsWrite7, outsideWrite2, 
                                       clientIdRead4, clockRead2, 
                                       clientIdRead5, clockRead3, 
                                       clientIdRead6, clockWrite2, keyRead0, 
                                       valueRead, clientIdRead7, clientIdRead8, 
                                       clockRead4, replicasWrite4, 
                                       replicasWrite5, clientsRead0, 
                                       clientsWrite8, clientsWrite9, 
                                       clientsWrite10, outsideWrite3, 
                                       clockWrite3, replicasWrite6, 
                                       clientsWrite11, outsideWrite4, 
                                       spinRead0, clockWrite4, replicasWrite7, 
                                       clientsWrite12, outsideWrite5, 
                                       clientIdRead9, clientIdRead10, 
                                       clockWrite5, replicasWrite8, 
                                       replicasWrite9, clientIdRead11, 
                                       clockRead5, clientIdRead12, clockRead6, 
                                       clientIdRead13, clockWrite6, 
                                       clientIdRead14, clientIdRead15, 
                                       clockRead7, replicasWrite10, 
                                       replicasWrite11, clockWrite7, 
                                       replicasWrite12, clockWrite8, 
                                       replicasWrite13, kvLocal, liveClients, 
                                       pendingRequests, stableMessages, i_, 
                                       firstPending, timestamp, nextClient, 
                                       lowestPending, chooseMessage, 
                                       currentClocks, minClock, continue_, 
                                       pendingClients, clientsIter, msg_, ok, 
                                       key, val, spinLocal, continue_G, getReq, 
                                       getResp, spinLocal0, continue_P, i, j_, 
                                       putReq, putResp, msg_D, j_D, spinLocal1, 
                                       j, msg >>

nullBroadcast(self) == /\ pc[self] = "nullBroadcast"
                       /\ clientIdRead11' = (self) - ((NUM_CLIENTS) * (NULL_ORDER))
                       /\ clockRead5' = clocks[clientIdRead11']
                       /\ IF ((j[self]) <= ((NUM_REPLICAS) - (1))) /\ ((clockRead5') # (-(1)))
                             THEN /\ (Len(replicasNetwork[j[self]])) < (BUFFER_SIZE)
                                  /\ replicasWrite10' = [replicasNetwork EXCEPT ![j[self]] = Append(replicasNetwork[j[self]], msg[self])]
                                  /\ j' = [j EXCEPT ![self] = (j[self]) + (1)]
                                  /\ replicasWrite11' = replicasWrite10'
                                  /\ replicasNetwork' = replicasWrite11'
                                  /\ pc' = [pc EXCEPT ![self] = "nullBroadcast"]
                             ELSE /\ replicasWrite11' = replicasNetwork
                                  /\ replicasNetwork' = replicasWrite11'
                                  /\ pc' = [pc EXCEPT ![self] = "nullCheckSpin"]
                                  /\ UNCHANGED << replicasWrite10, j >>
                       /\ UNCHANGED << allClients, clientMailboxes, cid, out, 
                                       clocks, replicasRead, replicasWrite, 
                                       kvRead, clientsWrite, clientsWrite0, 
                                       kvWrite, kvWrite0, clientsWrite1, 
                                       clientsWrite2, kvWrite1, replicasWrite0, 
                                       clientsWrite3, kvWrite2, clientIdRead, 
                                       clockRead, clientIdRead0, clockRead0, 
                                       clientIdRead1, clockWrite, keyRead, 
                                       clientIdRead2, clientIdRead3, 
                                       clockRead1, replicasWrite1, clientsRead, 
                                       clientsWrite4, outsideWrite, 
                                       clientsWrite5, outsideWrite0, 
                                       clockWrite0, replicasWrite2, 
                                       clientsWrite6, outsideWrite1, spinRead, 
                                       clockWrite1, replicasWrite3, 
                                       clientsWrite7, outsideWrite2, 
                                       clientIdRead4, clockRead2, 
                                       clientIdRead5, clockRead3, 
                                       clientIdRead6, clockWrite2, keyRead0, 
                                       valueRead, clientIdRead7, clientIdRead8, 
                                       clockRead4, replicasWrite4, 
                                       replicasWrite5, clientsRead0, 
                                       clientsWrite8, clientsWrite9, 
                                       clientsWrite10, outsideWrite3, 
                                       clockWrite3, replicasWrite6, 
                                       clientsWrite11, outsideWrite4, 
                                       spinRead0, clockWrite4, replicasWrite7, 
                                       clientsWrite12, outsideWrite5, 
                                       clientIdRead9, clientIdRead10, 
                                       clockWrite5, replicasWrite8, 
                                       replicasWrite9, clientIdRead12, 
                                       clockRead6, clientIdRead13, clockWrite6, 
                                       clientIdRead14, clientIdRead15, 
                                       clockRead7, clockWrite7, 
                                       replicasWrite12, spinRead1, clockWrite8, 
                                       replicasWrite13, kvLocal, liveClients, 
                                       pendingRequests, stableMessages, i_, 
                                       firstPending, timestamp, nextClient, 
                                       lowestPending, chooseMessage, 
                                       currentClocks, minClock, continue_, 
                                       pendingClients, clientsIter, msg_, ok, 
                                       key, val, spinLocal, continue_G, getReq, 
                                       getResp, spinLocal0, continue_P, i, j_, 
                                       putReq, putResp, msg_D, j_D, spinLocal1, 
                                       continue, msg >>

ClockUpdateClient(self) == clockUpdateLoop(self) \/ nullCheckSpin(self)
                              \/ nullBroadcast(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ReplicaSet: Replica(self))
           \/ (\E self \in GetSet: GetClient(self))
           \/ (\E self \in PutSet: PutClient(self))
           \/ (\E self \in DisconnectSet: DisconnectClient(self))
           \/ (\E self \in NullSet: ClockUpdateClient(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ReplicaSet : WF_vars(Replica(self))
        /\ \A self \in GetSet : WF_vars(GetClient(self))
        /\ \A self \in PutSet : WF_vars(PutClient(self))
        /\ \A self \in DisconnectSet : WF_vars(DisconnectClient(self))
        /\ \A self \in NullSet : WF_vars(ClockUpdateClient(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-bac0bd5a9581fcaaf62a0704717e8973

\* This predicate is true when all client processes are finished.
AllClientsDisconnected == \A client \in allClients : pc[client] = "Done"


\* Invariants
\* **********

\* These ensure that, in all states explored by TLC, the buffers (from client to replica and vice versa)
\* are within bounds. Using the FIFOChannel mapping macro is sufficient for this invariant to
\* hold.
BufferOk(net, node) == Len(net[node]) >= 0 /\ Len(net[node]) <= BUFFER_SIZE
ClientBuffersOk == \A node \in DOMAIN clientMailboxes : BufferOk(clientMailboxes, node)
ReplicaBuffersOk == \A node \in DOMAIN replicasNetwork : BufferOk(replicasNetwork, node)
AllBuffersOk == ClientBuffersOk /\ ReplicaBuffersOk

\* This invariant tests that message stability detection in the replica is safe:
\* every message considered stable must have a timestamp lower than the current logical
\* clock of any live client.
MessageStability == \A replica \in ReplicaSet :
                        LET stable == stableMessages[replica]
                            alive == { c \in ClientSet : clocks[c] > 0 }
                        IN
                            Len(stable) > 0 =>
                                \A m_id \in DOMAIN stable :
                                    \A client \in alive : stable[m_id].timestamp < clocks[client]


\* Put semantics: once a client has been notified that a Put request was succesful
\* every replica must have the updated value.
PersistentPut == \A client \in PutSet :
                     pc[client] = "putComplete" => \A replica \in ReplicaSet : kvLocal[replica][PUT_KEY] = PUT_VALUE


\* Properties
\* **********

\* Logical clocks are monotonically increasing. This property checks that in every state,
\* pending messages in the replicas have increasing timestamps (or the process disconnected)
ClockIncreased == clocks' /= clocks =>
                 \E c \in ClientSet : clocks'[c] = clocks[c]+1 \/ clocks'[c] = -1

MonotonicallyIncreasingClocks == [][ClockIncreased]_<<clocks>>


\* Safety of disconnection: once a client has disconnected (and sent a message to all replicas
\* informing of that event), then the logical clock of that client should remain
\* unchanced -- i.e., no more messages from that client should be seen in the system.
DisconnectionSafe == \A client \in ClientSet : <>[](clocks[client] = -1)

=============================================================================
\* Modification History
\* Last modified Mon Dec 21 03:02:11 PST 2020 by finn
\* Last modified Thu Apr 11 09:46:33 PDT 2019 by rmc
\* Last modified Wed Feb 27 12:42:52 PST 2019 by minh
