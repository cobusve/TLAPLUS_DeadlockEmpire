------------------------ MODULE UnsynchronizedCode3 ------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire
variables first = 0; second = 0;

process Left = 0
variable temp = 0
begin
L1: skip;
L2a: temp := first + 1;
L2b: first:= temp;
L3a: temp := second + 1;
L3b: second:= temp;
L4: if (second = 2 /\ first /= 2) then
L5:     skip;
    end if;
end process

process Right = 1
variable temp = 0
begin
R1a: temp := first + 1;
R1b: first:= temp;
R2a: temp := second + 1;
R2b: second:= temp;
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Process variable temp of process Left at line 8 col 10 changed to temp_
VARIABLES first, second, pc, temp_, temp

vars == << first, second, pc, temp_, temp >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ first = 0
        /\ second = 0
        (* Process Left *)
        /\ temp_ = 0
        (* Process Right *)
        /\ temp = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "L1"
                                        [] self = 1 -> "R1a"]

L1 == /\ pc[0] = "L1"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![0] = "L2a"]
      /\ UNCHANGED << first, second, temp_, temp >>

L2a == /\ pc[0] = "L2a"
       /\ temp_' = first + 1
       /\ pc' = [pc EXCEPT ![0] = "L2b"]
       /\ UNCHANGED << first, second, temp >>

L2b == /\ pc[0] = "L2b"
       /\ first' = temp_
       /\ pc' = [pc EXCEPT ![0] = "L3a"]
       /\ UNCHANGED << second, temp_, temp >>

L3a == /\ pc[0] = "L3a"
       /\ temp_' = second + 1
       /\ pc' = [pc EXCEPT ![0] = "L3b"]
       /\ UNCHANGED << first, second, temp >>

L3b == /\ pc[0] = "L3b"
       /\ second' = temp_
       /\ pc' = [pc EXCEPT ![0] = "L4"]
       /\ UNCHANGED << first, temp_, temp >>

L4 == /\ pc[0] = "L4"
      /\ IF (second = 2 /\ first /= 2)
            THEN /\ pc' = [pc EXCEPT ![0] = "L5"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << first, second, temp_, temp >>

L5 == /\ pc[0] = "L5"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << first, second, temp_, temp >>

Left == L1 \/ L2a \/ L2b \/ L3a \/ L3b \/ L4 \/ L5

R1a == /\ pc[1] = "R1a"
       /\ temp' = first + 1
       /\ pc' = [pc EXCEPT ![1] = "R1b"]
       /\ UNCHANGED << first, second, temp_ >>

R1b == /\ pc[1] = "R1b"
       /\ first' = temp
       /\ pc' = [pc EXCEPT ![1] = "R2a"]
       /\ UNCHANGED << second, temp_, temp >>

R2a == /\ pc[1] = "R2a"
       /\ temp' = second + 1
       /\ pc' = [pc EXCEPT ![1] = "R2b"]
       /\ UNCHANGED << first, second, temp_ >>

R2b == /\ pc[1] = "R2b"
       /\ second' = temp
       /\ pc' = [pc EXCEPT ![1] = "Done"]
       /\ UNCHANGED << first, temp_, temp >>

Right == R1a \/ R1b \/ R2a \/ R2b

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

DeadlockCondition == {pc[0]} /= {"L5"}

=============================================================================
\* Modification History
\* Last modified Mon Apr 01 00:04:28 PDT 2019 by ejacobus
\* Created Sun Mar 31 23:04:12 PDT 2019 by ejacobus
