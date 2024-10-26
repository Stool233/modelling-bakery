---- MODULE DistributedBakery ----
EXTENDS Naturals, Sequences, FiniteSets
VARIABLES nums, views, in_cs, acks, queues
CONSTANTS N
----
Peers == 1..N

AckMsg == N+1

TypeOk == /\ nums \in [Peers -> Nat]
          /\ views \in [Peers -> [Peers -> Nat]]
          /\ in_cs \in SUBSET Peers
          /\ acks \in [Peers -> [Peers -> BOOLEAN]]
          /\ queues \in [Peers -> Seq(Peers \X Nat)]

\* The mutex invariant.
MutexInvariant == Cardinality(in_cs) \in {0,1}

\* The inductive invariant explaining why the mutex invariant holds.
BakeryInvariant == /\ \A p1 \in Peers:
                    /\ nums[p1] > 0 => \A p2 \in Peers \ {p1}:
                        \/ nums[p2] = 0
                        \/ (acks[p1][p2] => views[p2][p1] = nums[p1])
                            /\ (acks[p2][p1] => views[p1][p2] = nums[p2])

Init == /\ nums = [peer \in Peers |-> 0]
        /\ views = [peer \in Peers |-> [t \in Peers |-> 0]]
        /\ in_cs = {}
        /\ acks = [peer \in Peers |-> [t \in Peers |-> FALSE]]
        /\ queues = [peers \in Peers |-> <<>>]

StartChoosing(id) ==
    LET max[i \in Peers] == IF i = 1 THEN views[id][i]
                            ELSE IF views[id][i] > max[i-1] THEN views[id][i]
                            ELSE max[i-1] 
        maxNum == max[N] + 1
    IN  /\ nums[id] = 0
        /\ nums' = [nums EXCEPT ![id] = maxNum]
        /\ acks' = [acks EXCEPT ![id] = [t \in Peers |-> FALSE]]
        /\ queues' = [p \in Peers |-> Append(queues[p], <<id, maxNum>>)]
        /\ UNCHANGED <<in_cs, views>>


EnterCs(id) ==
    LET min[i \in Peers] == IF i = N THEN views[id][i]
                            ELSE IF views[id][i] < min[i+1] THEN views[id][i]
                            ELSE min[i+1]
        minNum == min[N]
    IN  /\ nums[id] > 0
        /\ nums[id] = minNum
        \* All other peers must have ack'ed,
        \* and if another peers chose the minimum,
        \* break the tie by id.
        /\ \A p \in Peers \ {id}:
            /\ acks[id][p] = TRUE
            /\ IF views[id][p] = minNum THEN p > id ELSE TRUE
        /\ in_cs' = in_cs \cup {id}
        /\ UNCHANGED <<nums, views, acks, queues>>

ExitCs(id) == /\ id \in in_cs
              /\ nums' = [nums EXCEPT ![id] = 0]
              /\ in_cs' = in_cs \ {id}
              \* Send the zero to all peers, including id.
              /\ queues' = [p \in Peers |-> Append(queues[p], <<id, 0>>)]
              /\ UNCHANGED <<acks, views>>

HandleMsg(id) == LET msg == Head(queues[id])
                 IN /\ Len(queues[id]) > 0
                    /\ CASE msg[2] = AckMsg ->
                            \* Note the acknowledgement.
                            /\ acks' = [acks EXCEPT ![id][msg[1]] = TRUE]
                            /\ queues' = [queues EXCEPT ![id] = Tail(@)]
                            /\ UNCHANGED <<nums, views, in_cs>>
                         [] msg[2] \in Peers ->
                            \* Note the number,
                            \* send an acknowledgement.
                            /\ views' = [views EXCEPT ![id][msg[1]] = msg[2]]
                            /\ queues' = [queues EXCEPT 
                                                    ![id] = Tail(@),
                                                    ![msg[1]] = Append(@, <<id, AckMsg>>)]
                            /\ UNCHANGED <<nums, acks, in_cs>>
                         [] msg[2] = 0 ->
                            \* Note the zero.
                            /\ views' = [views EXCEPT ![id][msg[1]] = msg[2]]
                            /\ UNCHANGED <<nums, acks, queues, in_cs>>

\* End with inifinite stuttering steps
Stop == /\ \E id \in Peers: nums[id] = N
        /\ UNCHANGED <<nums, views, in_cs, acks, queues>>

Next == \/ \E id \in Peers: \/ StartChoosing(id)
                            \/ EnterCs(id)
                            \/ ExitCs(id)
                            \/ HandleMsg(id)
        \/ Stop
----
Spec == Init /\ [][Next]_<<nums, views, in_cs, acks, queues>>

THEOREM Spec => [](TypeOk /\ MutexInvariant /\ BakeryInvariant)
====
