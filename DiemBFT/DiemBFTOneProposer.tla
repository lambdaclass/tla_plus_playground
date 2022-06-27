------------------------- MODULE DiemBFTOneProposer -------------------------
EXTENDS Naturals, Integers, FiniteSets


(***************************************************************************)
(*  Global Constants and Variables                                         *)
(***************************************************************************)
CONSTANTS    
    R,          \* Max number of rounds
    isLeader,   \* Function that tells if the node is selected as a leader in the round
    F           \* Number of Byzantine nodes

VARIABLES 
    round,      \* Current round
    roundStates,\* Mapping from round to the status of the current round
    votersPerRound

(***************************************************************************)
(* Helper Predicates                                                       *)
(***************************************************************************)
Rounds == 0..R
Voters == 0..(3*F)

MAXIMUM(S) == CHOOSE x \in S : \A y \in S : x >= y
MAX(a, b) == IF a > b THEN a ELSE b

ValidRoundStates == {"NOT_STARTED", "IGNORED", "PROPOSED"}
AllProposalMessages == [r: Rounds]

CanPropose == roundStates[round] = "NOT_STARTED" /\ isLeader[round]

AreMajority(V) == Cardinality(V) = (2*F + 1)

(***************************************************************************)
(* Formal Spec of Init State and Next State                                *)
(***************************************************************************)
Proposal(proposalMsg) == /\ CanPropose
                         /\ proposalMsg.r = round
                         /\ roundStates' = [roundStates EXCEPT ![round] = "PROPOSED"]
                         /\ UNCHANGED <<round, votersPerRound>>

receiveVote(v, r) == /\ r >= round
                     /\ LET roundVoters == votersPerRound[r] \union {v} IN (
                        /\ votersPerRound' = [votersPerRound EXCEPT ![r] = roundVoters]
                        /\ (IF AreMajority(roundVoters) THEN
                            /\ round' = r + 1
                          ELSE
                            /\ round' = r)
                        )
                     /\ UNCHANGED <<roundStates>>
                        
skipRound == ~isLeader[round]
           /\ roundStates' = [roundStates EXCEPT![round] = "IGNORED"]
           /\ round' = round + 1
           /\ UNCHANGED <<votersPerRound>>

(***************************************************************************)
(* This is not explained in the paper, but in the first round the leader   *)
(* node for the first round sends a proposal message, otherwise all nodes  *)
(* would get stuck waiting for an event to occur                           *)
(***************************************************************************)
Init == /\ round = 1
        /\ roundStates = [n \in Rounds \union {R+1} |-> "NOT_STARTED"]        
        /\ votersPerRound = [n \in Rounds \union {R+1} |-> {}]
        /\ IF CanPropose THEN
            \E proposalMsg \in AllProposalMessages : (
                /\ isLeader[round]
                /\  Proposal(proposalMsg)
            )
           ELSE
            skipRound
     
(***************************************************************************)
(* In this particular model, we consider that the proposer node skips      *)
(* rounds in which it is not a leader.  Also, listens for votes and makes  *)
(* proposals in rounds it is the leader                                    *)
(***************************************************************************)
Next == \/ \E proposalMsg \in AllProposalMessages : Proposal(proposalMsg)
        \/ \E v \in Voters, r \in Rounds : receiveVote(v, r)
        \/ skipRound

\** Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == /\ round \in Nat
          /\ \A r \in Rounds : roundStates[r] \in ValidRoundStates
          

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 12:21:48 ART 2022 by lambda
\* Created Tue Jun 21 18:17:50 ART 2022 by lambda
