-------------------------- MODULE DeadlockEmpire2 --------------------------


EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire2
variables a = 0; critical_section = 0;

process Left \in 1..2
variable temp = 0
begin
L1: temp := a + 1;
L2: a := temp;
L3: if a = 1 then
      critical_section := critical_section + 1;
      L4:
         critical_section := critical_section - 1;
    end if 
end process

end algorithm *)

\* BEGIN TRANSLATION
VARIABLES a, critical_section, pc, temp

vars == << a, critical_section, pc, temp >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ a = 0
        /\ critical_section = 0
        (* Process Left *)
        /\ temp = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ temp' = [temp EXCEPT ![self] = a + 1]
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << a, critical_section >>

L2(self) == /\ pc[self] = "L2"
            /\ a' = temp[self]
            /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << critical_section, temp >>

L3(self) == /\ pc[self] = "L3"
            /\ IF a = 1
                  THEN /\ critical_section' = critical_section + 1
                       /\ pc' = [pc EXCEPT ![self] = "L4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED critical_section
            /\ UNCHANGED << a, temp >>

L4(self) == /\ pc[self] = "L4"
            /\ critical_section' = critical_section - 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << a, temp >>

Left(self) == L1(self) \/ L2(self) \/ L3(self) \/ L4(self)

Next == (\E self \in 1..2: Left(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

DeadlockCondition == critical_section <= 1

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 22:49:43 PDT 2019 by ejacobus
\* Created Sun Mar 31 22:26:28 PDT 2019 by ejacobus
