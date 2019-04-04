----------------------------- MODULE BossFight -----------------------------
EXTENDS Naturals, TLC, Sequences

(* --algorithm DeadlockEmpire
variables  darkness = 0; evil = 0; fortressCounter = 0; sanctumMutex = 0; sanctumPulse = 0;


macro Monitor_enter() begin
    await sanctumMutex = 0;                    \*    Monitor.Enter(sanctum);
    sanctumMutex := sanctumMutex + 1;
end macro;

macro Monitor_exit() begin
    sanctumMutex := sanctumMutex - 1;          \*    Monitor.Exit(sanctum);
end macro;

macro Monitor_wait() begin
    Monitor_exit();
    await sanctumPulse = 1;                    \*    Monitor.Wait(sanctum);
end macro;


process Left = 1
variable temp = 0
begin
L1: while (TRUE) do
L2:   temp := darkness + 1;
L3:   darkness := temp;
L4:   temp := evil + 1;
L5:   evil := temp; 
L6:   if ( darkness /= 2 /\ evil /= 2 ) then           \* if (darkness != 2 && evil != 2)
L7:     if ( fortressCounter > 0 ) then                \*  if (fortress.Wait(500)) 
            fortressCounter := fortressCounter - 1;
L8:         await ( fortressCounter > 0 );             \*    fortress.Wait();
            fortressCounter := fortressCounter - 1;
L9:         Monitor_enter();
L10:        Monitor_wait();
L12:        Monitor_enter();
L13:        skip;
L14:        sanctumMutex := sanctumMutex - 1;          \*    Monitor.Exit(sanctum);
        end if;
      end if;
    end while;
end process;


process Right = 2
variable temp = 0
begin
R1: while (TRUE) do
R2:   temp := darkness + 1;
R3:   darkness := temp;
R4:   temp := evil + 1;
R5:   evil := temp;
R6:   if ( darkness /= 2 /\ evil = 2 ) then     \* if (darkness != 2 && evil == 2)
R7:     Monitor_enter();
R8:     sanctumPulse := 1;                      \*    Monitor.Pulse(sanctum)
R9:     sanctumPulse := 0;
R10:    Monitor_exit();
R11:    skip;
      end if;
R12:  fortressCounter := fortressCounter + 1;
R13:  darkness := 0;
R14:  evil := 0;
    end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Process variable temp of process Left at line 24 col 10 changed to temp_
VARIABLES darkness, evil, fortressCounter, sanctumMutex, sanctumPulse, pc, 
          temp_, temp

vars == << darkness, evil, fortressCounter, sanctumMutex, sanctumPulse, pc, 
           temp_, temp >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ darkness = 0
        /\ evil = 0
        /\ fortressCounter = 0
        /\ sanctumMutex = 0
        /\ sanctumPulse = 0
        (* Process Left *)
        /\ temp_ = 0
        (* Process Right *)
        /\ temp = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "L1"
                                        [] self = 2 -> "R1"]

L1 == /\ pc[1] = "L1"
      /\ pc' = [pc EXCEPT ![1] = "L2"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp_, temp >>

L2 == /\ pc[1] = "L2"
      /\ temp_' = darkness + 1
      /\ pc' = [pc EXCEPT ![1] = "L3"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp >>

L3 == /\ pc[1] = "L3"
      /\ darkness' = temp_
      /\ pc' = [pc EXCEPT ![1] = "L4"]
      /\ UNCHANGED << evil, fortressCounter, sanctumMutex, sanctumPulse, temp_, 
                      temp >>

L4 == /\ pc[1] = "L4"
      /\ temp_' = evil + 1
      /\ pc' = [pc EXCEPT ![1] = "L5"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp >>

L5 == /\ pc[1] = "L5"
      /\ evil' = temp_
      /\ pc' = [pc EXCEPT ![1] = "L6"]
      /\ UNCHANGED << darkness, fortressCounter, sanctumMutex, sanctumPulse, 
                      temp_, temp >>

L6 == /\ pc[1] = "L6"
      /\ IF ( darkness /= 2 /\ evil /= 2 )
            THEN /\ pc' = [pc EXCEPT ![1] = "L7"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "L1"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp_, temp >>

L7 == /\ pc[1] = "L7"
      /\ IF ( fortressCounter > 0 )
            THEN /\ fortressCounter' = fortressCounter - 1
                 /\ pc' = [pc EXCEPT ![1] = "L8"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "L1"]
                 /\ UNCHANGED fortressCounter
      /\ UNCHANGED << darkness, evil, sanctumMutex, sanctumPulse, temp_, temp >>

L8 == /\ pc[1] = "L8"
      /\ ( fortressCounter > 0 )
      /\ fortressCounter' = fortressCounter - 1
      /\ pc' = [pc EXCEPT ![1] = "L9"]
      /\ UNCHANGED << darkness, evil, sanctumMutex, sanctumPulse, temp_, temp >>

L9 == /\ pc[1] = "L9"
      /\ sanctumMutex = 0
      /\ sanctumMutex' = sanctumMutex + 1
      /\ pc' = [pc EXCEPT ![1] = "L10"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumPulse, temp_, 
                      temp >>

L10 == /\ pc[1] = "L10"
       /\ sanctumMutex' = sanctumMutex - 1
       /\ sanctumPulse = 1
       /\ pc' = [pc EXCEPT ![1] = "L12"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumPulse, temp_, 
                       temp >>

L12 == /\ pc[1] = "L12"
       /\ sanctumMutex = 0
       /\ sanctumMutex' = sanctumMutex + 1
       /\ pc' = [pc EXCEPT ![1] = "L13"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumPulse, temp_, 
                       temp >>

L13 == /\ pc[1] = "L13"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "L14"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                       sanctumPulse, temp_, temp >>

L14 == /\ pc[1] = "L14"
       /\ sanctumMutex' = sanctumMutex - 1
       /\ pc' = [pc EXCEPT ![1] = "L1"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumPulse, temp_, 
                       temp >>

Left == L1 \/ L2 \/ L3 \/ L4 \/ L5 \/ L6 \/ L7 \/ L8 \/ L9 \/ L10 \/ L12
           \/ L13 \/ L14

R1 == /\ pc[2] = "R1"
      /\ pc' = [pc EXCEPT ![2] = "R2"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp_, temp >>

R2 == /\ pc[2] = "R2"
      /\ temp' = darkness + 1
      /\ pc' = [pc EXCEPT ![2] = "R3"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp_ >>

R3 == /\ pc[2] = "R3"
      /\ darkness' = temp
      /\ pc' = [pc EXCEPT ![2] = "R4"]
      /\ UNCHANGED << evil, fortressCounter, sanctumMutex, sanctumPulse, temp_, 
                      temp >>

R4 == /\ pc[2] = "R4"
      /\ temp' = evil + 1
      /\ pc' = [pc EXCEPT ![2] = "R5"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp_ >>

R5 == /\ pc[2] = "R5"
      /\ evil' = temp
      /\ pc' = [pc EXCEPT ![2] = "R6"]
      /\ UNCHANGED << darkness, fortressCounter, sanctumMutex, sanctumPulse, 
                      temp_, temp >>

R6 == /\ pc[2] = "R6"
      /\ IF ( darkness /= 2 /\ evil = 2 )
            THEN /\ pc' = [pc EXCEPT ![2] = "R9"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "R14"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                      sanctumPulse, temp_, temp >>

R9 == /\ pc[2] = "R9"
      /\ sanctumMutex = 0
      /\ sanctumMutex' = sanctumMutex + 1
      /\ pc' = [pc EXCEPT ![2] = "R10"]
      /\ UNCHANGED << darkness, evil, fortressCounter, sanctumPulse, temp_, 
                      temp >>

R10 == /\ pc[2] = "R10"
       /\ sanctumPulse' = 1
       /\ pc' = [pc EXCEPT ![2] = "R11"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, temp_, 
                       temp >>

R11 == /\ pc[2] = "R11"
       /\ sanctumPulse' = 0
       /\ pc' = [pc EXCEPT ![2] = "R12"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, temp_, 
                       temp >>

R12 == /\ pc[2] = "R12"
       /\ sanctumMutex' = sanctumMutex - 1
       /\ pc' = [pc EXCEPT ![2] = "R13"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumPulse, temp_, 
                       temp >>

R13 == /\ pc[2] = "R13"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![2] = "R14"]
       /\ UNCHANGED << darkness, evil, fortressCounter, sanctumMutex, 
                       sanctumPulse, temp_, temp >>

R14 == /\ pc[2] = "R14"
       /\ fortressCounter' = fortressCounter + 1
       /\ pc' = [pc EXCEPT ![2] = "R15"]
       /\ UNCHANGED << darkness, evil, sanctumMutex, sanctumPulse, temp_, temp >>

R15 == /\ pc[2] = "R15"
       /\ darkness' = 0
       /\ pc' = [pc EXCEPT ![2] = "R16"]
       /\ UNCHANGED << evil, fortressCounter, sanctumMutex, sanctumPulse, 
                       temp_, temp >>

R16 == /\ pc[2] = "R16"
       /\ evil' = 0
       /\ pc' = [pc EXCEPT ![2] = "R1"]
       /\ UNCHANGED << darkness, fortressCounter, sanctumMutex, sanctumPulse, 
                       temp_, temp >>

Right == R1 \/ R2 \/ R3 \/ R4 \/ R5 \/ R6 \/ R9 \/ R10 \/ R11 \/ R12 \/ R13
            \/ R14 \/ R15 \/ R16

Next == Left \/ Right
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

CriticalSections == {pc[1],pc[2]} /= {"L13", "R13"}

=============================================================================
\* Modification History
\* Last modified Wed Apr 03 17:10:17 PDT 2019 by ejacobus
\* Created Mon Apr 01 01:15:27 PDT 2019 by ejacobus
