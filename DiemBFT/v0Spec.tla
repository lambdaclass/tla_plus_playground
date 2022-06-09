------------------------------- MODULE v0Spec -------------------------------

EXTENDS Naturals

CONSTANTS
    Honest,         \* The set of "Good" nodes
    Byzantine,      \* The set of Byzantine nodes
    F              \* The number (or upper bound actually) of Byzantine nodes
    
VARIABLES 
    round, 
    leader,
    roundResult,
    roundProposal
    
vars == <<round, leader, roundResult, roundProposal>>
    
ValidProposal == "Valid"
InvalidProposal == "Invalid"

Nodes == Honest \union Byzantine \* The set of all nodes

ChangeLeader == leader # leader' /\ leader' \in Nodes 
            /\ UNCHANGED <<round, roundResult, roundProposal>>

Init == round = 0 /\ Honest \intersect Byzantine = {} /\ leader \in Nodes

Next == TRUE

Spec == Init /\ [][Next]_vars
    
=============================================================================
\* Modification History
\* Last modified Thu Jun 09 16:03:26 ART 2022 by lambda
\* Created Thu Jun 09 15:16:39 ART 2022 by lambda
