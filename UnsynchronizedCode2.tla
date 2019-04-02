------------------------ MODULE UnsynchronizedCode2 ------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire
variables counter = 0;

process Left = 0
begin
L1: while (TRUE) do
L2:   counter := counter + 1;
L3:   if (counter = 5) then
L4:     skip;
      end if;
    end while;
end process

process Right = 1
begin
R1: while (TRUE) do
R2:   counter := counter + 1;
R3:   if (counter = 3) then
R4:     skip;
      end if;
    end while;
end process

end algorithm *)

\* BEGIN TRANSLATION
VARIABLES counter, pc

vars == << counter, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ counter = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "L1"
                                        [] self = 1 -> "R1"]

L1 == /\ pc[0] = "L1"
      /\ pc' = [pc EXCEPT ![0] = "L2"]
      /\ UNCHANGED counter

L2 == /\ pc[0] = "L2"
      /\ counter' = counter + 1
      /\ pc' = [pc EXCEPT ![0] = "L3"]

L3 == /\ pc[0] = "L3"
      /\ IF (counter = 5)
            THEN /\ pc' = [pc EXCEPT ![0] = "L4"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "L1"]
      /\ UNCHANGED counter

L4 == /\ pc[0] = "L4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![0] = "L1"]
      /\ UNCHANGED counter

Left == L1 \/ L2 \/ L3 \/ L4

R1 == /\ pc[1] = "R1"
      /\ pc' = [pc EXCEPT ![1] = "R2"]
      /\ UNCHANGED counter

R2 == /\ pc[1] = "R2"
      /\ counter' = counter + 1
      /\ pc' = [pc EXCEPT ![1] = "R3"]

R3 == /\ pc[1] = "R3"
      /\ IF (counter = 3)
            THEN /\ pc' = [pc EXCEPT ![1] = "R4"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "R1"]
      /\ UNCHANGED counter

R4 == /\ pc[1] = "R4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "R1"]
      /\ UNCHANGED counter

Right == R1 \/ R2 \/ R3 \/ R4

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

DeadlockCondition == {pc[0],pc[1]} /= {"L4", "R4"}

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 23:53:10 PDT 2019 by ejacobus
\* Created Sun Mar 31 23:04:12 PDT 2019 by ejacobus
