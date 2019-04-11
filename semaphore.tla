----------------------------- MODULE semaphore -----------------------------
EXTENDS Integers, TLC
(*--algorithm criticalSection 
variables semaphore = 2; p1InCriticalSection = FALSE; p2InCriticalSection = FALSE;

\* https://deadlockempire.github.io/#S1-simple

\* invariants to check
define
    DoubleEnterCriticalSection == p1InCriticalSection = FALSE \/ p2InCriticalSection = FALSE
end define;

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
P1_3:   p1InCriticalSection := TRUE;
P1_4:   p1InCriticalSection := FALSE;
P1_5:   semaphoreGive(1);
    end while;
end process;

process p2 = 1
begin
P2_1: while (TRUE) do 
P2_2:   semaphoreTake(1);
P2_3:   p2InCriticalSection := TRUE;
P2_4:   p2InCriticalSection := FALSE;
P2_5:   semaphoreGive(1);     
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES semaphore, p1InCriticalSection, p2InCriticalSection, pc

(* define statement *)
DoubleEnterCriticalSection == p1InCriticalSection = FALSE \/ p2InCriticalSection = FALSE


vars == << semaphore, p1InCriticalSection, p2InCriticalSection, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ semaphore = 2
        /\ p1InCriticalSection = FALSE
        /\ p2InCriticalSection = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P1_1"
                                        [] self = 1 -> "P2_1"]

P1_1 == /\ pc[0] = "P1_1"
        /\ pc' = [pc EXCEPT ![0] = "P1_2"]
        /\ UNCHANGED << semaphore, p1InCriticalSection, p2InCriticalSection >>

P1_2 == /\ pc[0] = "P1_2"
        /\ ( semaphore >= 1 )
        /\ semaphore' = semaphore - 1
        /\ pc' = [pc EXCEPT ![0] = "P1_3"]
        /\ UNCHANGED << p1InCriticalSection, p2InCriticalSection >>

P1_3 == /\ pc[0] = "P1_3"
        /\ p1InCriticalSection' = TRUE
        /\ pc' = [pc EXCEPT ![0] = "P1_4"]
        /\ UNCHANGED << semaphore, p2InCriticalSection >>

P1_4 == /\ pc[0] = "P1_4"
        /\ p1InCriticalSection' = FALSE
        /\ pc' = [pc EXCEPT ![0] = "P1_5"]
        /\ UNCHANGED << semaphore, p2InCriticalSection >>

P1_5 == /\ pc[0] = "P1_5"
        /\ semaphore' = semaphore + 1
        /\ pc' = [pc EXCEPT ![0] = "P1_1"]
        /\ UNCHANGED << p1InCriticalSection, p2InCriticalSection >>

p1 == P1_1 \/ P1_2 \/ P1_3 \/ P1_4 \/ P1_5

P2_1 == /\ pc[1] = "P2_1"
        /\ pc' = [pc EXCEPT ![1] = "P2_2"]
        /\ UNCHANGED << semaphore, p1InCriticalSection, p2InCriticalSection >>

P2_2 == /\ pc[1] = "P2_2"
        /\ ( semaphore >= 1 )
        /\ semaphore' = semaphore - 1
        /\ pc' = [pc EXCEPT ![1] = "P2_3"]
        /\ UNCHANGED << p1InCriticalSection, p2InCriticalSection >>

P2_3 == /\ pc[1] = "P2_3"
        /\ p2InCriticalSection' = TRUE
        /\ pc' = [pc EXCEPT ![1] = "P2_4"]
        /\ UNCHANGED << semaphore, p1InCriticalSection >>

P2_4 == /\ pc[1] = "P2_4"
        /\ p2InCriticalSection' = FALSE
        /\ pc' = [pc EXCEPT ![1] = "P2_5"]
        /\ UNCHANGED << semaphore, p1InCriticalSection >>

P2_5 == /\ pc[1] = "P2_5"
        /\ semaphore' = semaphore + 1
        /\ pc' = [pc EXCEPT ![1] = "P2_1"]
        /\ UNCHANGED << p1InCriticalSection, p2InCriticalSection >>

p2 == P2_1 \/ P2_2 \/ P2_3 \/ P2_4 \/ P2_5

Next == p1 \/ p2
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Apr 11 00:21:00 PDT 2019 by yuhzheng
\* Created Wed Apr 10 23:40:01 PDT 2019 by yuhzheng
