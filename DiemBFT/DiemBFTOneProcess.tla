------------------------- MODULE DiemBFTOneProcess -------------------------
EXTENDS Naturals, Integers

CONSTANTS     
    R           \* Max number of round

VARIABLES 
    nodeState,  \* Mapping of a round r to the state of the proposal, 
                \* the states are defined in ValidRoundStates.
    round,      \* Current round
    QCs         \* Set of received QCs

ValidRoundStates == {"UNSEEN", "PREVOTE", "PRECOMMIT", "COMMIT", "COMMITED"}
Rounds == 0..R
TypeOK == /\ round \in Nat
          /\ QCs \subseteq [r: Rounds, prevQC: Rounds \union {-1}]
          /\ nodeState \in [Rounds -> ValidRoundStates]

MAXIMUM(S) == CHOOSE x \in S : \A y \in S : x >= y
MAX(a, b) == IF a > b THEN a ELSE b

AllQCs == [r: Rounds, prevQC: Rounds \union {-1}]

Init == /\ round = 0
        /\ QCs = {}
        /\ nodeState = [n \in Rounds |-> "UNSEEN"]

ExistsQC(r) == \E qc \in QCs : (qc.r = r)

RoundReady(r) == nodeState' = [nodeState EXCEPT![r] = "PREVOTE"]
RoundPreVoted(r) == nodeState' = [nodeState EXCEPT![r] = "PRECOMMIT"]
RoundPreCommited(r) == nodeState' = [nodeState EXCEPT![r] = "COMMIT", ![r+1] = "PRECOMMIT"]
RoundCommited(r) == nodeState' = [nodeState EXCEPT![r] = "COMMITED", ![r+1] = "COMMIT", ![r+2] = "PRECOMMIT"]
      
NewQC(qc) == /\ qc.r >= round
             /\ (
                    \/ (qc.prevQC = -1 /\ qc.r = 0) 
                    \/ (round > 0 /\ ExistsQC(qc.prevQC) /\ qc.prevQC = round - 1)
                )  
             /\ qc \notin QCs
             /\ IF qc.r >= 2 /\ ExistsQC(qc.r-1) /\ ExistsQC(qc.r-2)
               THEN RoundCommited(qc.r-2)
               ELSE IF qc.r >= 1 /\ ExistsQC(qc.r-1)
               THEN RoundPreCommited(qc.r-1)
               ELSE RoundPreVoted(qc.r)
             /\ QCs' = QCs \union {qc}
        
Next == \/ /\ \E qc \in AllQCs :(
                /\  NewQC(qc)
                /\  round' = qc.r + 1
             )

=============================================================================
\* Modification History
\* Last modified Mon Jun 13 14:47:52 ART 2022 by lambda
\* Created Mon Jun 13 08:53:58 ART 2022 by lambda
