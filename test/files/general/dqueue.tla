----------------------------- MODULE dqueue -----------------------------
(***************************************************************************)
(* Distributed queue using Modular PlusCal.                                *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC

CONSTANTS BUFFER_SIZE, NUM_CONSUMERS, PRODUCER


(***************************************************************************
--mpcal dqueue {
  define {
    (* total nodes in the system: number of consumers + the producer *)
    NUM_NODES == NUM_CONSUMERS + 1
  }

  mapping macro TCPChannel {
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

  mapping macro CyclicReads {
      read  {
          $variable := ($variable + 1) % BUFFER_SIZE;
          yield $variable;

      }

      write { yield $variable }
  }

  (* consumer: Processes one element read from the network at a time, infinitely *)
  archetype AConsumer(ref net[_], ref proc) {
      c: while (TRUE) {
          (* request more data to the producer by sending your own identifier
             over the network *)
          c1: net[PRODUCER] := self;

          (* processes the piece of data the producer sends back over the network
             by writing to a "processor" abstract interface *)
          c2: proc := net[self];
      }
  }

  archetype AProducer(ref net[_], ref s)
  variable requester; {
      p: while (TRUE) {
          (* wait for a consumer to request data *)
          p1: requester := net[self];

          (* send some data to the requester coming from a "stream" abstract interface *)
          p2: net[requester] := s;
      }
  }

  variables network = [id \in 0..NUM_NODES-1 |-> <<>>],
            processor = 0,
            stream = 0;

  fair process (Consumer \in 1..NUM_CONSUMERS) == instance AConsumer(ref network[_], ref processor)
      mapping network[_] via TCPChannel;
  fair process (Producer \in {PRODUCER}) == instance AProducer(ref network[_], ref stream)
      mapping network[_] via TCPChannel
      mapping stream via CyclicReads;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm dqueue {
    variables network = [id \in (0) .. ((NUM_NODES) - (1)) |-> <<>>], processor = 0, stream = 0, netWrite, netRead, procWrite, netWrite0, procWrite0, netRead0, netWrite1, sRead, sWrite, netWrite2, sWrite0;
    define {
        NUM_NODES == (NUM_CONSUMERS) + (1)
    }
    fair process (Consumer \in (1) .. (NUM_CONSUMERS))
    {
        c:
            if (TRUE) {
                c1:
                    await (Len(network[PRODUCER])) < (BUFFER_SIZE);
                    netWrite := [network EXCEPT ![PRODUCER] = Append(network[PRODUCER], self)];
                    network := netWrite;

                c2:
                    await (Len(network[self])) > (0);
                    with (msg0 = Head(network[self])) {
                        netWrite := [network EXCEPT ![self] = Tail(network[self])];
                        netRead := msg0;
                    };
                    procWrite := netRead;
                    network := netWrite;
                    processor := procWrite;
                    goto c;

            } else {
                netWrite0 := network;
                procWrite0 := processor;
                network := netWrite0;
                processor := procWrite0;
            };

    }
    fair process (Producer \in {PRODUCER})
    variables requester;
    {
        p:
            if (TRUE) {
                p1:
                    await (Len(network[self])) > (0);
                    with (msg1 = Head(network[self])) {
                        netWrite1 := [network EXCEPT ![self] = Tail(network[self])];
                        netRead0 := msg1;
                    };
                    requester := netRead0;
                    network := netWrite1;

                p2:
                    sWrite := ((stream) + (1)) % (BUFFER_SIZE);
                    sRead := sWrite;
                    await (Len(network[requester])) < (BUFFER_SIZE);
                    netWrite1 := [network EXCEPT ![requester] = Append(network[requester], sRead)];
                    network := netWrite1;
                    stream := sWrite;
                    goto p;

            } else {
                netWrite2 := network;
                sWrite0 := stream;
                network := netWrite2;
                stream := sWrite0;
            };

    }
}
\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION PCal-e64ab9284c1a4c5172f564abb6f099c4
CONSTANT defaultInitValue
VARIABLES network, processor, stream, netWrite, netRead, procWrite, netWrite0, 
          procWrite0, netRead0, netWrite1, sRead, sWrite, netWrite2, sWrite0, 
          pc

(* define statement *)
NUM_NODES == (NUM_CONSUMERS) + (1)

VARIABLE requester

vars == << network, processor, stream, netWrite, netRead, procWrite, 
           netWrite0, procWrite0, netRead0, netWrite1, sRead, sWrite, 
           netWrite2, sWrite0, pc, requester >>

ProcSet == ((1) .. (NUM_CONSUMERS)) \cup ({PRODUCER})

Init == (* Global variables *)
        /\ network = [id \in (0) .. ((NUM_NODES) - (1)) |-> <<>>]
        /\ processor = 0
        /\ stream = 0
        /\ netWrite = defaultInitValue
        /\ netRead = defaultInitValue
        /\ procWrite = defaultInitValue
        /\ netWrite0 = defaultInitValue
        /\ procWrite0 = defaultInitValue
        /\ netRead0 = defaultInitValue
        /\ netWrite1 = defaultInitValue
        /\ sRead = defaultInitValue
        /\ sWrite = defaultInitValue
        /\ netWrite2 = defaultInitValue
        /\ sWrite0 = defaultInitValue
        (* Process Producer *)
        /\ requester = [self \in {PRODUCER} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in (1) .. (NUM_CONSUMERS) -> "c"
                                        [] self \in {PRODUCER} -> "p"]

c(self) == /\ pc[self] = "c"
           /\ IF TRUE
                 THEN /\ pc' = [pc EXCEPT ![self] = "c1"]
                      /\ UNCHANGED << network, processor, netWrite0, 
                                      procWrite0 >>
                 ELSE /\ netWrite0' = network
                      /\ procWrite0' = processor
                      /\ network' = netWrite0'
                      /\ processor' = procWrite0'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << stream, netWrite, netRead, procWrite, netRead0, 
                           netWrite1, sRead, sWrite, netWrite2, sWrite0, 
                           requester >>

c1(self) == /\ pc[self] = "c1"
            /\ (Len(network[PRODUCER])) < (BUFFER_SIZE)
            /\ netWrite' = [network EXCEPT ![PRODUCER] = Append(network[PRODUCER], self)]
            /\ network' = netWrite'
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << processor, stream, netRead, procWrite, netWrite0, 
                            procWrite0, netRead0, netWrite1, sRead, sWrite, 
                            netWrite2, sWrite0, requester >>

c2(self) == /\ pc[self] = "c2"
            /\ (Len(network[self])) > (0)
            /\ LET msg0 == Head(network[self]) IN
                 /\ netWrite' = [network EXCEPT ![self] = Tail(network[self])]
                 /\ netRead' = msg0
            /\ procWrite' = netRead'
            /\ network' = netWrite'
            /\ processor' = procWrite'
            /\ pc' = [pc EXCEPT ![self] = "c"]
            /\ UNCHANGED << stream, netWrite0, procWrite0, netRead0, netWrite1, 
                            sRead, sWrite, netWrite2, sWrite0, requester >>

Consumer(self) == c(self) \/ c1(self) \/ c2(self)

p(self) == /\ pc[self] = "p"
           /\ IF TRUE
                 THEN /\ pc' = [pc EXCEPT ![self] = "p1"]
                      /\ UNCHANGED << network, stream, netWrite2, sWrite0 >>
                 ELSE /\ netWrite2' = network
                      /\ sWrite0' = stream
                      /\ network' = netWrite2'
                      /\ stream' = sWrite0'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << processor, netWrite, netRead, procWrite, netWrite0, 
                           procWrite0, netRead0, netWrite1, sRead, sWrite, 
                           requester >>

p1(self) == /\ pc[self] = "p1"
            /\ (Len(network[self])) > (0)
            /\ LET msg1 == Head(network[self]) IN
                 /\ netWrite1' = [network EXCEPT ![self] = Tail(network[self])]
                 /\ netRead0' = msg1
            /\ requester' = [requester EXCEPT ![self] = netRead0']
            /\ network' = netWrite1'
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << processor, stream, netWrite, netRead, procWrite, 
                            netWrite0, procWrite0, sRead, sWrite, netWrite2, 
                            sWrite0 >>

p2(self) == /\ pc[self] = "p2"
            /\ sWrite' = ((stream) + (1)) % (BUFFER_SIZE)
            /\ sRead' = sWrite'
            /\ (Len(network[requester[self]])) < (BUFFER_SIZE)
            /\ netWrite1' = [network EXCEPT ![requester[self]] = Append(network[requester[self]], sRead')]
            /\ network' = netWrite1'
            /\ stream' = sWrite'
            /\ pc' = [pc EXCEPT ![self] = "p"]
            /\ UNCHANGED << processor, netWrite, netRead, procWrite, netWrite0, 
                            procWrite0, netRead0, netWrite2, sWrite0, 
                            requester >>

Producer(self) == p(self) \/ p1(self) \/ p2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (1) .. (NUM_CONSUMERS): Consumer(self))
           \/ (\E self \in {PRODUCER}: Producer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in (1) .. (NUM_CONSUMERS) : WF_vars(Consumer(self))
        /\ \A self \in {PRODUCER} : WF_vars(Producer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION TLA-3b32e33f9317d9065792b6369f21a56b
=============================================================================
\* Modification History
\* Last modified Fri Dec 18 02:02:58 PST 2020 by finn
\* Last modified Mon Apr 01 02:11:17 PDT 2019 by minh
\* Last modified Tue Jan 22 18:38:13 PST 2019 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
