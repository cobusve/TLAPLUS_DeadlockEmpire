------------------------- MODULE producer_consumer -------------------------
EXTENDS Integers, TLC
(*--algorithm producer_consumer 
variables semaphore=0; i = 0;

define
    QueueInconsistent == i >= 0
    \*SchedulingFairness == i < 10
end define;

\* https://deadlockempire.github.io/#S2-producerConsumer

macro semaphoreTake(n) begin
    await ( semaphore >= n );
    semaphore := semaphore - n;
end macro;

macro semaphoreGive(n) begin
    semaphore := semaphore + n;
end macro;

process producer = 0
begin
P1: while (TRUE) do
P2:     semaphoreGive(1);    
P3:     i := i + 1;
    end while;
end process;

process consumer = 1
begin
C1: while (TRUE) do 
C2:     semaphoreTake(1);
C3:     i := i - 1;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES semaphore, i, pc

(* define statement *)
QueueInconsistent == i >= 0


vars == << semaphore, i, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ semaphore = 0
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P1"
                                        [] self = 1 -> "C1"]

P1 == /\ pc[0] = "P1"
      /\ pc' = [pc EXCEPT ![0] = "P2"]
      /\ UNCHANGED << semaphore, i >>

P2 == /\ pc[0] = "P2"
      /\ semaphore' = semaphore + 1
      /\ pc' = [pc EXCEPT ![0] = "P3"]
      /\ i' = i

P3 == /\ pc[0] = "P3"
      /\ i' = i + 1
      /\ pc' = [pc EXCEPT ![0] = "P1"]
      /\ UNCHANGED semaphore

producer == P1 \/ P2 \/ P3

C1 == /\ pc[1] = "C1"
      /\ pc' = [pc EXCEPT ![1] = "C2"]
      /\ UNCHANGED << semaphore, i >>

C2 == /\ pc[1] = "C2"
      /\ ( semaphore >= 1 )
      /\ semaphore' = semaphore - 1
      /\ pc' = [pc EXCEPT ![1] = "C3"]
      /\ i' = i

C3 == /\ pc[1] = "C3"
      /\ i' = i - 1
      /\ pc' = [pc EXCEPT ![1] = "C1"]
      /\ UNCHANGED semaphore

consumer == C1 \/ C2 \/ C3

Next == producer \/ consumer
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Apr 10 23:35:59 PDT 2019 by yuhzheng
\* Created Wed Apr 10 22:25:54 PDT 2019 by yuhzheng
