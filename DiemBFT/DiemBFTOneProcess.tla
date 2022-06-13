------------------------- MODULE DiemBFTOneProcess -------------------------
EXTENDS Naturals, Integers

VARIABLES 
    nodeState,  \* Mapping of a round r to the state of the proposal
    round,      \* Current round
    QCs         \* Set of received QCs

ValidRoundStates == {"UNSEEN", "PREVOTE", "PRECOMMIT", "COMMIT", "COMMITED"}
MAXIMUM(S) == CHOOSE x \in S : \A y \in S : x >= y
AllQCs == [r: Nat, prevQC: Nat]

TypeOK == /\ round \in Nat
          /\ QCs \in SUBSET [r: Nat, prevQC: Nat]
          /\ nodeState \in [Nat -> ValidRoundStates]

Init == /\ round = 0
        /\ QCs = {}
        /\ nodeState = [n \in Nat |-> "UNSEEN"]

ExistsQC(r) == \E qc \in QCs : qc.r = r


RoundCommited(r) == nodeState[r]' = "COMMITED"
      
NewQC(qc) == /\ qc.r >= round
             /\ qc.prevQC \in QCs  
             /\ qc \notin QCs
             /\ IF round > 2 /\ ExistsQC(round-1) /\ ExistsQC(round-2)
               THEN RoundCommited(round-2)
               ELSE TRUE
             /\ QCs' = QCs \union {qc}
        
NEXT == \/ /\ \E qc \in AllQCs : NewQC(qc)
           /\ round' = round + 1

=============================================================================
\* Modification History
\* Last modified Mon Jun 13 11:10:09 ART 2022 by lambda
\* Created Mon Jun 13 08:53:58 ART 2022 by lambda
