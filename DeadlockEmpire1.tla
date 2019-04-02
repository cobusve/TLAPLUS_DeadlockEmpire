-------------------------- MODULE DeadlockEmpire1 --------------------------


EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire1
variables business = 0; flag = 1

process Left = 0
begin
L1: business := 1;
LCS: skip;
L4: business := 2;
end process

process Right = 1
begin
R1: 
   if flag = 1 then 
      RCS: skip;
   end if;
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label cs of process Left at line 12 col 5 changed to cs_
VARIABLES business, flag, pc

vars == << business, flag, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ business = 0
        /\ flag = 1
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "L1"
                                        [] self = 1 -> "R1"]

L1 == /\ pc[0] = "L1"
      /\ business' = 1
      /\ pc' = [pc EXCEPT ![0] = "cs_"]
      /\ flag' = flag

cs_ == /\ pc[0] = "cs_"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![0] = "L4"]
       /\ UNCHANGED << business, flag >>

L4 == /\ pc[0] = "L4"
      /\ business' = 2
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ flag' = flag

Left == L1 \/ cs_ \/ L4

R1 == /\ pc[1] = "R1"
      /\ IF flag = 1
            THEN /\ pc' = [pc EXCEPT ![1] = "cs"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << business, flag >>

cs == /\ pc[1] = "cs"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << business, flag >>

Right == R1 \/ cs

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

DeadlockCondition == {pc[0],pc[1]} /= {"LCS","RCS"}

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 23:22:06 PDT 2019 by ejacobus
\* Created Sun Mar 31 22:26:28 PDT 2019 by ejacobus
