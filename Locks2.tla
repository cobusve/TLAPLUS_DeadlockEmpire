------------------------------- MODULE Locks2 -------------------------------
EXTENDS Naturals, TLC

(* --algorithm DeadlockEmpire
variables mutex = 0; mutex2 = 0; mutex3 = 0;
mutexOwner = 0; mutex2Owner = 0; mutex3Owner = 0; flag = FALSE

process Left = 1
variable temp = 0
begin
L1: while (TRUE) do
L2:   if (mutex = 0 \/ (mutexOwner = 1)) then              \* Monitor.TryEnter(mutex);
         mutex := mutex + 1; 
         mutexOwner := 1;
L3:      await (mutex3 = 0 \/ mutex3Owner = 1);            \* Monitor.Enter(mutex3);
         mutex3 := mutex3 + 1;
         mutex3Owner := 1;
L4:      await (mutex = 0 \/ mutexOwner = 1);               \* Monitor.Enter(mutex);
         mutex := mutex + 1; 
         mutexOwner := 1;
L5:      skip;
L6:      mutex:= mutex - 1;                                 \* Monitor.Exit(mutex);
         if (mutex = 0) then mutexOwner := 0; end if;
L7:      await (mutex2 = 0 \/ mutex2Owner = 1);             \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 1;
L8:      flag := FALSE;
L9:      mutex2 := mutex2 - 1;                              \* Monitor.Exit(mutex2);
         if (mutex2 = 0) then mutex2Owner := 0; end if;
L10:     mutex3 := mutex3 - 1;                              \* Monitor.Exit(mutex3);
         if (mutex3 = 0) then mutex3Owner := 0; end if;
      else 
L11:     await (mutex2 = 0 \/ mutex2Owner = 1);             \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 1;
L12:     flag := TRUE;
L13:     mutex2:= mutex2 - 1;                               \* Monitor.Exit(mutex2);
         if (mutex2 = 0) then mutex2Owner := 0; end if;
      end if;
    end while;
end process;


process Right = 2
variable temp = 0
begin
R1: while (TRUE) do
R2:   if (flag) then
R3:      await (mutex2 = 0 \/ mutex2Owner = 2);      \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 2;
R4:      await (mutex = 0 \/ mutexOwner = 2);        \* Monitor.Enter(mutex);
         mutex := mutex + 1; 
         mutexOwner := 2;
R5:      flag := FALSE;
R5b:     skip;
R6:      mutex:= mutex - 1;                          \* Monitor.Exit(mutex);
         if (mutex = 0) then mutexOwner := 0; end if;   
R7:      await (mutex2 = 0 \/ mutex2Owner = 2);      \* Monitor.Enter(mutex2);
         mutex2 := mutex2 + 1; 
         mutex2Owner := 2;
      else 
R8:      await (mutex = 0 \/ mutexOwner = 2);        \* Monitor.Enter(mutex);
         mutex := mutex + 1; 
         mutexOwner := 2;  
R9:      flag := FALSE;
R10:     mutex:= mutex - 1;                          \* Monitor.Exit(mutex);
         if (mutex = 0) then mutexOwner := 0; end if;   
      end if;
    end while;
end process;
    
end algorithm *)
\* BEGIN TRANSLATION
\* Process variable temp of process Left at line 9 col 10 changed to temp_
VARIABLES mutex, mutex2, mutex3, mutexOwner, mutex2Owner, mutex3Owner, flag, 
          pc, temp_, temp

vars == << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, mutex3Owner, flag, 
           pc, temp_, temp >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ mutex = 0
        /\ mutex2 = 0
        /\ mutex3 = 0
        /\ mutexOwner = 0
        /\ mutex2Owner = 0
        /\ mutex3Owner = 0
        /\ flag = FALSE
        (* Process Left *)
        /\ temp_ = 0
        (* Process Right *)
        /\ temp = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "L1"
                                        [] self = 2 -> "R1"]

L1 == /\ pc[1] = "L1"
      /\ pc' = [pc EXCEPT ![1] = "L2"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, flag, temp_, temp >>

L2 == /\ pc[1] = "L2"
      /\ IF (mutex = 0 \/ (mutexOwner = 1))
            THEN /\ mutex' = mutex + 1
                 /\ mutexOwner' = 1
                 /\ pc' = [pc EXCEPT ![1] = "L3"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "L11"]
                 /\ UNCHANGED << mutex, mutexOwner >>
      /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                      temp >>

L3 == /\ pc[1] = "L3"
      /\ (mutex3 = 0 \/ mutex3Owner = 1)
      /\ mutex3' = mutex3 + 1
      /\ mutex3Owner' = 1
      /\ pc' = [pc EXCEPT ![1] = "L4"]
      /\ UNCHANGED << mutex, mutex2, mutexOwner, mutex2Owner, flag, temp_, 
                      temp >>

L4 == /\ pc[1] = "L4"
      /\ (mutex = 0 \/ mutexOwner = 1)
      /\ mutex' = mutex + 1
      /\ mutexOwner' = 1
      /\ pc' = [pc EXCEPT ![1] = "L5"]
      /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                      temp >>

L5 == /\ pc[1] = "L5"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "L6"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, flag, temp_, temp >>

L6 == /\ pc[1] = "L6"
      /\ mutex' = mutex - 1
      /\ IF (mutex' = 0)
            THEN /\ mutexOwner' = 0
            ELSE /\ TRUE
                 /\ UNCHANGED mutexOwner
      /\ pc' = [pc EXCEPT ![1] = "L7"]
      /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                      temp >>

L7 == /\ pc[1] = "L7"
      /\ (mutex2 = 0 \/ mutex2Owner = 1)
      /\ mutex2' = mutex2 + 1
      /\ mutex2Owner' = 1
      /\ pc' = [pc EXCEPT ![1] = "L8"]
      /\ UNCHANGED << mutex, mutex3, mutexOwner, mutex3Owner, flag, temp_, 
                      temp >>

L8 == /\ pc[1] = "L8"
      /\ flag' = FALSE
      /\ pc' = [pc EXCEPT ![1] = "L9"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, temp_, temp >>

L9 == /\ pc[1] = "L9"
      /\ mutex2' = mutex2 - 1
      /\ IF (mutex2' = 0)
            THEN /\ mutex2Owner' = 0
            ELSE /\ TRUE
                 /\ UNCHANGED mutex2Owner
      /\ pc' = [pc EXCEPT ![1] = "L10"]
      /\ UNCHANGED << mutex, mutex3, mutexOwner, mutex3Owner, flag, temp_, 
                      temp >>

L10 == /\ pc[1] = "L10"
       /\ mutex3' = mutex3 - 1
       /\ IF (mutex3' = 0)
             THEN /\ mutex3Owner' = 0
             ELSE /\ TRUE
                  /\ UNCHANGED mutex3Owner
       /\ pc' = [pc EXCEPT ![1] = "L1"]
       /\ UNCHANGED << mutex, mutex2, mutexOwner, mutex2Owner, flag, temp_, 
                       temp >>

L11 == /\ pc[1] = "L11"
       /\ (mutex2 = 0 \/ mutex2Owner = 1)
       /\ mutex2' = mutex2 + 1
       /\ mutex2Owner' = 1
       /\ pc' = [pc EXCEPT ![1] = "L12"]
       /\ UNCHANGED << mutex, mutex3, mutexOwner, mutex3Owner, flag, temp_, 
                       temp >>

L12 == /\ pc[1] = "L12"
       /\ flag' = TRUE
       /\ pc' = [pc EXCEPT ![1] = "L13"]
       /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                       mutex3Owner, temp_, temp >>

L13 == /\ pc[1] = "L13"
       /\ mutex2' = mutex2 - 1
       /\ IF (mutex2' = 0)
             THEN /\ mutex2Owner' = 0
             ELSE /\ TRUE
                  /\ UNCHANGED mutex2Owner
       /\ pc' = [pc EXCEPT ![1] = "L1"]
       /\ UNCHANGED << mutex, mutex3, mutexOwner, mutex3Owner, flag, temp_, 
                       temp >>

Left == L1 \/ L2 \/ L3 \/ L4 \/ L5 \/ L6 \/ L7 \/ L8 \/ L9 \/ L10 \/ L11
           \/ L12 \/ L13

R1 == /\ pc[2] = "R1"
      /\ pc' = [pc EXCEPT ![2] = "R2"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, flag, temp_, temp >>

R2 == /\ pc[2] = "R2"
      /\ IF (flag)
            THEN /\ pc' = [pc EXCEPT ![2] = "R3"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "R8"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, flag, temp_, temp >>

R3 == /\ pc[2] = "R3"
      /\ (mutex2 = 0 \/ mutex2Owner = 2)
      /\ mutex2' = mutex2 + 1
      /\ mutex2Owner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R4"]
      /\ UNCHANGED << mutex, mutex3, mutexOwner, mutex3Owner, flag, temp_, 
                      temp >>

R4 == /\ pc[2] = "R4"
      /\ (mutex = 0 \/ mutexOwner = 2)
      /\ mutex' = mutex + 1
      /\ mutexOwner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R5"]
      /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                      temp >>

R5 == /\ pc[2] = "R5"
      /\ flag' = FALSE
      /\ pc' = [pc EXCEPT ![2] = "R5b"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, temp_, temp >>

R5b == /\ pc[2] = "R5b"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![2] = "R6"]
       /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                       mutex3Owner, flag, temp_, temp >>

R6 == /\ pc[2] = "R6"
      /\ mutex' = mutex - 1
      /\ IF (mutex' = 0)
            THEN /\ mutexOwner' = 0
            ELSE /\ TRUE
                 /\ UNCHANGED mutexOwner
      /\ pc' = [pc EXCEPT ![2] = "R7"]
      /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                      temp >>

R7 == /\ pc[2] = "R7"
      /\ (mutex2 = 0 \/ mutex2Owner = 2)
      /\ mutex2' = mutex2 + 1
      /\ mutex2Owner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R1"]
      /\ UNCHANGED << mutex, mutex3, mutexOwner, mutex3Owner, flag, temp_, 
                      temp >>

R8 == /\ pc[2] = "R8"
      /\ (mutex = 0 \/ mutexOwner = 2)
      /\ mutex' = mutex + 1
      /\ mutexOwner' = 2
      /\ pc' = [pc EXCEPT ![2] = "R9"]
      /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                      temp >>

R9 == /\ pc[2] = "R9"
      /\ flag' = FALSE
      /\ pc' = [pc EXCEPT ![2] = "R10"]
      /\ UNCHANGED << mutex, mutex2, mutex3, mutexOwner, mutex2Owner, 
                      mutex3Owner, temp_, temp >>

R10 == /\ pc[2] = "R10"
       /\ mutex' = mutex - 1
       /\ IF (mutex' = 0)
             THEN /\ mutexOwner' = 0
             ELSE /\ TRUE
                  /\ UNCHANGED mutexOwner
       /\ pc' = [pc EXCEPT ![2] = "R1"]
       /\ UNCHANGED << mutex2, mutex3, mutex2Owner, mutex3Owner, flag, temp_, 
                       temp >>

Right == R1 \/ R2 \/ R3 \/ R4 \/ R5 \/ R5b \/ R6 \/ R7 \/ R8 \/ R9 \/ R10

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Assertions == mutex >= 0 /\ mutex2 >= 0 /\ mutex3 >= 0 
CriticalSections == {pc[1],pc[2]} /= {"L5", "R5b"}

=============================================================================
\* Modification History
\* Last modified Tue Apr 02 01:04:30 PDT 2019 by ejacobus
\* Created Mon Apr 01 01:15:27 PDT 2019 by ejacobus
