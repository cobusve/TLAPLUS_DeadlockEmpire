------------------------------- MODULE HighLevelSync1 -------------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire
variables sync = 0; counter = 0;

process Left = 1
begin
L1:   while TRUE do
L2:      await sync = 1;
L3:      if ( counter % 2 = 1) then
L4:          skip;
         end if;
      end while;
end process;


process Right = 2
begin
R1:   while TRUE do
R2:      sync := 0;
R3:      counter := counter + 1;
R4:      counter := counter + 1;
R5:      sync := 1;
      end while;
end process;
    
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES sync, counter, pc

vars == << sync, counter, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ sync = 0
        /\ counter = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "L1"
                                        [] self = 2 -> "R1"]

L1 == /\ pc[1] = "L1"
      /\ pc' = [pc EXCEPT ![1] = "L2"]
      /\ UNCHANGED << sync, counter >>

L2 == /\ pc[1] = "L2"
      /\ sync = 1
      /\ pc' = [pc EXCEPT ![1] = "L3"]
      /\ UNCHANGED << sync, counter >>

L3 == /\ pc[1] = "L3"
      /\ IF ( counter % 2 = 1)
            THEN /\ pc' = [pc EXCEPT ![1] = "L4"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "L1"]
      /\ UNCHANGED << sync, counter >>

L4 == /\ pc[1] = "L4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "L1"]
      /\ UNCHANGED << sync, counter >>

Left == L1 \/ L2 \/ L3 \/ L4

R1 == /\ pc[2] = "R1"
      /\ pc' = [pc EXCEPT ![2] = "R2"]
      /\ UNCHANGED << sync, counter >>

R2 == /\ pc[2] = "R2"
      /\ sync' = 0
      /\ pc' = [pc EXCEPT ![2] = "R3"]
      /\ UNCHANGED counter

R3 == /\ pc[2] = "R3"
      /\ counter' = counter + 1
      /\ pc' = [pc EXCEPT ![2] = "R4"]
      /\ sync' = sync

R4 == /\ pc[2] = "R4"
      /\ counter' = counter + 1
      /\ pc' = [pc EXCEPT ![2] = "R5"]
      /\ sync' = sync

R5 == /\ pc[2] = "R5"
      /\ sync' = 1
      /\ pc' = [pc EXCEPT ![2] = "R1"]
      /\ UNCHANGED counter

Right == R1 \/ R2 \/ R3 \/ R4 \/ R5

Next == Left \/ Right

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

FailureCondition == {pc[1]} /= {"L4"}

=============================================================================
\* Modification History
\* Last modified Tue Apr 02 01:24:28 PDT 2019 by ejacobus
\* Created Mon Apr 01 01:15:27 PDT 2019 by ejacobus
