import R1Z.RomObserverBin

/-! The operational observer handoff must identify the source query program.
Preserving the decision function alone does not preserve execution history. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitObserverBoundary
open R1Z.GamesR1

def oneQuery (address : List UInt8) : OProg := .query address (fun _ => .done)

/-- An allowed observer replacement changes the complete history, for every
oracle and every existing prior, as soon as one query is available. -/
theorem replacement_changes_history (prior : List (List UInt8 × R0Z.FsStatement.OracleAnswer))
    (address : List UInt8) (oracle : List UInt8 → R0Z.FsStatement.OracleAnswer) (fuel : Nat) :
    prior ++ runLog .done oracle (fuel+1) ≠
      prior ++ runLog (oneQuery address) oracle (fuel+1) := by
  intro same
  have length := congrArg List.length same
  simp only [runLog, oneQuery, List.length_append, List.length_nil,
    List.length_cons] at length
  omega

/-- The obstruction is independent of the chosen prior and oracle answers;
there is no universal suffix-history theorem for an unrestricted handoff. -/
theorem no_unrestricted_history_transport
    (oracle : List UInt8 → R0Z.FsStatement.OracleAnswer) (fuel : Nat) :
    ¬ (∀ (source observer : OProg) (prior : List (List UInt8 × R0Z.FsStatement.OracleAnswer)),
      prior ++ runLog source oracle (fuel+1) =
        prior ++ runLog observer oracle (fuel+1)) := by
  intro all
  exact replacement_changes_history [] [] oracle fuel (all .done (oneQuery []) [])

#print axioms replacement_changes_history
#print axioms no_unrestricted_history_transport
end R1Z.ProverCommitObserverBoundary
