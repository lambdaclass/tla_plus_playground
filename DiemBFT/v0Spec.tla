------------------------------- MODULE v0Spec -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES 
    round,
    lastQCRound, 
    lastTCRound
    
vars == <<round, lastQCRound, lastTCRound>>

TypeOK ==   /\ round \in Nat
            /\ lastQCRound \in Nat
            /\ lastTCRound \in Nat

Init == /\ round = 0
        /\ lastTCRound = 0 
        /\ lastQCRound = 0

increaseRound ==  /\ round' = round + 1
                  /\ UNCHANGED <<lastTCRound, lastQCRound>>

commit ==   /\ round > lastQCRound
            /\ round > lastTCRound
            /\ lastQCRound' = round 
            /\ UNCHANGED <<round, lastTCRound>>

timeout ==   /\ round > lastQCRound
            /\ round > lastTCRound
            /\ lastTCRound' = round 
            /\ UNCHANGED <<round, lastQCRound>>

Next == \/ commit 
        \/ timeout 
        \/ increaseRound

Spec == Init /\ [][Next]_vars
    
=============================================================================
\* Modification History
\* Last modified Fri Jun 10 12:29:07 ART 2022 by lambda
\* Created Thu Jun 09 15:16:39 ART 2022 by lambda
