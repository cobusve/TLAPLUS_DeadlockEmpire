------------------------------- MODULE Locks2 -------------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire
variables mutex = 0; mutex2 = 0;
mutexOwner = 0; mutex2Owner = 0; 

process Left = 1
begin
L1:      await (mutex = 0 \/ mutexOwner = 1);               \* Monitor.Enter(mutex);
         mutex := mutex + 1; 
         mutexOwner := 1;
L2:      await (mutex2 = 0 \/ mutex2Owner = 1);             \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 1;
L3:      skip;
L4:      mutex := mutex - 1;                              \* Monitor.Exit(mutex);
         if (mutex = 0) then mutexOwner := 0; end if;
L5:      mutex2 := mutex2 - 1;                              \* Monitor.Exit(mutex2);
         if (mutex2 = 0) then mutex2Owner := 0; end if;
end process;


process Right = 2
begin
R1:      await (mutex2 = 0 \/ mutex2Owner = 2);      \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 2;
R2:      await (mutex = 0 \/ mutexOwner = 2);        \* Monitor.Enter(mutex);
         mutex := mutex + 1; 
         mutexOwner := 2;
R3:     skip;
R4:      await (mutex2 = 0 \/ mutex2Owner = 2);      \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 2;
R5:      mutex:= mutex - 1;                          \* Monitor.Exit(mutex);
         if (mutex = 0) then mutexOwner := 0; end if;   
end process;
    
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES mutex, mutex2, mutexOwner, mutex2Owner, pc

vars == << mutex, mutex2, mutexOwner, mutex2Owner, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ mutex = 0
        /\ mutex2 = 0
        /\ mutexOwner = 0
        /\ mutex2Owner = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "L1"
                                        [] self = 2 -> "R1"]

L1 == /\ pc[1] = "L1"
      /\ (mutex = 0 \/ mutexOwner = 1)
      /\ mutex' = mutex + 1
      /\ mutexOwner' = 1
      /\ pc' = [pc EXCEPT ![1] = "L2"]
      /\ UNCHANGED << mutex2, mutex2Owner >>

L2 == /\ pc[1] = "L2"
      /\ (mutex2 = 0 \/ mutex2Owner = 1)
      /\ mutex2' = mutex2 + 1
      /\ mutex2Owner' = 1
      /\ pc' = [pc EXCEPT ![1] = "L3"]
      /\ UNCHANGED << mutex, mutexOwner >>

L3 == /\ pc[1] = "L3"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "L4"]
      /\ UNCHANGED << mutex, mutex2, mutexOwner, mutex2Owner >>

L4 == /\ pc[1] = "L4"
      /\ mutex' = mutex - 1
      /\ IF (mutex' = 0)
            THEN /\ mutexOwner' = 0
            ELSE /\ TRUE
                 /\ UNCHANGED mutexOwner
      /\ pc' = [pc EXCEPT ![1] = "L5"]
      /\ UNCHANGED << mutex2, mutex2Owner >>

L5 == /\ pc[1] = "L5"
      /\ mutex2' = mutex2 - 1
      /\ IF (mutex2' = 0)
            THEN /\ mutex2Owner' = 0
            ELSE /\ TRUE
                 /\ UNCHANGED mutex2Owner
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << mutex, mutexOwner >>

Left == L1 \/ L2 \/ L3 \/ L4 \/ L5

R1 == /\ pc[2] = "R1"
      /\ (mutex2 = 0 \/ mutex2Owner = 2)
      /\ mutex2' = mutex2 + 1
      /\ mutex2Owner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R2"]
      /\ UNCHANGED << mutex, mutexOwner >>

R2 == /\ pc[2] = "R2"
      /\ (mutex = 0 \/ mutexOwner = 2)
      /\ mutex' = mutex + 1
      /\ mutexOwner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R3"]
      /\ UNCHANGED << mutex2, mutex2Owner >>

R3 == /\ pc[2] = "R3"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "R4"]
      /\ UNCHANGED << mutex, mutex2, mutexOwner, mutex2Owner >>

R4 == /\ pc[2] = "R4"
      /\ (mutex2 = 0 \/ mutex2Owner = 2)
      /\ mutex2' = mutex2 + 1
      /\ mutex2Owner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R5"]
      /\ UNCHANGED << mutex, mutexOwner >>

R5 == /\ pc[2] = "R5"
      /\ mutex' = mutex - 1
      /\ IF (mutex' = 0)
            THEN /\ mutexOwner' = 0
            ELSE /\ TRUE
                 /\ UNCHANGED mutexOwner
      /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << mutex2, mutex2Owner >>

Right == R1 \/ R2 \/ R3 \/ R4 \/ R5

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Assertions == mutex >= 0 /\ mutex2 >= 0
CriticalSections == {pc[1],pc[2]} /= {"L3", "R3"}

=============================================================================
\* Modification History
\* Last modified Tue Apr 02 01:13:13 PDT 2019 by ejacobus
\* Created Mon Apr 01 01:15:27 PDT 2019 by ejacobus
