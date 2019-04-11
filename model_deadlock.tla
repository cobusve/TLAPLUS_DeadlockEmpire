--------------------------- MODULE model_deadlock ---------------------------
EXTENDS Integers, TLC
(*--algorithm tla_deadlock 
variables semaphore = 0; 

\* A demonstration of TLA model checker deadlock.
macro semaphoreTake(n) begin
    await ( semaphore >= n );
    semaphore := semaphore - n;
end macro;

macro semaphoreGive(n) begin
    semaphore := semaphore + n;
end macro;

process p1 = 0
begin
P1_1: while (TRUE) do
P1_2:   semaphoreTake(1); 
P1_3:   semaphoreGive(1);
    end while;
end process;

process p2 = 1
begin
P2_1: while (TRUE) do 
P2_2:   semaphoreTake(1);
P2_3:   semaphoreGive(1);     
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES semaphore, pc

vars == << semaphore, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ semaphore = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P1_1"
                                        [] self = 1 -> "P2_1"]

P1_1 == /\ pc[0] = "P1_1"
        /\ pc' = [pc EXCEPT ![0] = "P1_2"]
        /\ UNCHANGED semaphore

P1_2 == /\ pc[0] = "P1_2"
        /\ ( semaphore >= 1 )
        /\ semaphore' = semaphore - 1
        /\ pc' = [pc EXCEPT ![0] = "P1_3"]

P1_3 == /\ pc[0] = "P1_3"
        /\ semaphore' = semaphore + 1
        /\ pc' = [pc EXCEPT ![0] = "P1_1"]

p1 == P1_1 \/ P1_2 \/ P1_3

P2_1 == /\ pc[1] = "P2_1"
        /\ pc' = [pc EXCEPT ![1] = "P2_2"]
        /\ UNCHANGED semaphore

P2_2 == /\ pc[1] = "P2_2"
        /\ ( semaphore >= 1 )
        /\ semaphore' = semaphore - 1
        /\ pc' = [pc EXCEPT ![1] = "P2_3"]

P2_3 == /\ pc[1] = "P2_3"
        /\ semaphore' = semaphore + 1
        /\ pc' = [pc EXCEPT ![1] = "P2_1"]

p2 == P2_1 \/ P2_2 \/ P2_3

Next == p1 \/ p2
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Apr 11 00:15:21 PDT 2019 by yuhzheng
\* Created Thu Apr 11 00:13:08 PDT 2019 by yuhzheng
