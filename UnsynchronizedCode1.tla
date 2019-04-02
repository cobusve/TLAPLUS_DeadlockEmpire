------------------------ MODULE UnsynchronizedCode1 ------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire2
variables flag = FALSE;

process Left \in 0..1
begin
L1: while (flag /= FALSE) do
      skip; 
    end while;
L2: flag := TRUE; 
L3: skip;
L4: flag := FALSE;
end process

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES flag, pc

vars == << flag, pc >>

ProcSet == (0..1)

Init == (* Global variables *)
        /\ flag = FALSE
        /\ pc = [self \in ProcSet |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ IF (flag /= FALSE)
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "L1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ flag' = flag

L2(self) == /\ pc[self] = "L2"
            /\ flag' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "L3"]

L3(self) == /\ pc[self] = "L3"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "L4"]
            /\ flag' = flag

L4(self) == /\ pc[self] = "L4"
            /\ flag' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "Done"]

Left(self) == L1(self) \/ L2(self) \/ L3(self) \/ L4(self)

Next == (\E self \in 0..1: Left(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

DeadlockCondition == {pc[0],pc[1]} /= {"L3"}

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 23:47:10 PDT 2019 by ejacobus
\* Created Sun Mar 31 23:04:12 PDT 2019 by ejacobus
