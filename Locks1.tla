------------------------------- MODULE Locks1 -------------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire
variables mutex = 0; i = 0;

process Left = 0
begin
L1: while (TRUE) do
L2:   await mutex = 0; mutex := 1;  \* Await with an assignment atomically emulates a mutex
L3:   i := i + 2;
L4:   skip;
L5:   if ( i = 5 ) then
L6:      skip;
      end if;
L7:   mutex := 0;  \* Release mutex
    end while;
end process

process Right = 1
begin
R1: while (TRUE) do
R2:   await mutex = 0; mutex := 1;
R3:   i := i - 1;
R4:   skip;
R5:   mutex := 0;  \* Release mutex
    end while;
end process
    
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES mutex, i, pc

vars == << mutex, i, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ mutex = 0
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "L1"
                                        [] self = 1 -> "R1"]

L1 == /\ pc[0] = "L1"
      /\ pc' = [pc EXCEPT ![0] = "L2"]
      /\ UNCHANGED << mutex, i >>

L2 == /\ pc[0] = "L2"
      /\ mutex = 0
      /\ mutex' = 1
      /\ pc' = [pc EXCEPT ![0] = "L3"]
      /\ i' = i

L3 == /\ pc[0] = "L3"
      /\ i' = i + 2
      /\ pc' = [pc EXCEPT ![0] = "L4"]
      /\ mutex' = mutex

L4 == /\ pc[0] = "L4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![0] = "L5"]
      /\ UNCHANGED << mutex, i >>

L5 == /\ pc[0] = "L5"
      /\ IF ( i = 5 )
            THEN /\ pc' = [pc EXCEPT ![0] = "L6"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "L7"]
      /\ UNCHANGED << mutex, i >>

L6 == /\ pc[0] = "L6"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![0] = "L7"]
      /\ UNCHANGED << mutex, i >>

L7 == /\ pc[0] = "L7"
      /\ mutex' = 0
      /\ pc' = [pc EXCEPT ![0] = "L1"]
      /\ i' = i

Left == L1 \/ L2 \/ L3 \/ L4 \/ L5 \/ L6 \/ L7

R1 == /\ pc[1] = "R1"
      /\ pc' = [pc EXCEPT ![1] = "R2"]
      /\ UNCHANGED << mutex, i >>

R2 == /\ pc[1] = "R2"
      /\ mutex = 0
      /\ mutex' = 1
      /\ pc' = [pc EXCEPT ![1] = "R3"]
      /\ i' = i

R3 == /\ pc[1] = "R3"
      /\ i' = i - 1
      /\ pc' = [pc EXCEPT ![1] = "R4"]
      /\ mutex' = mutex

R4 == /\ pc[1] = "R4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "R5"]
      /\ UNCHANGED << mutex, i >>

R5 == /\ pc[1] = "R5"
      /\ mutex' = 0
      /\ pc' = [pc EXCEPT ![1] = "R1"]
      /\ i' = i

Right == R1 \/ R2 \/ R3 \/ R4 \/ R5

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

DeadlockCondition == {pc[0],pc[1]} /= {"L4", "R4"} 
Assertion == pc[0] /= "L6"

=============================================================================
\* Modification History
\* Last modified Mon Apr 01 18:41:38 PDT 2019 by ejacobus
\* Created Mon Apr 01 01:15:27 PDT 2019 by ejacobus
