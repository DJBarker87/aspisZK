import R1Z.PV_RJQ_FinishQueries
import R1Z.PV_RunJoin_PublishSkeleton57
set_option autoImplicit false
namespace R1Z.PV_RJQ_QueryRange
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PublishSkeleton54 PV_RunJoin_PublishSkeleton57
variable [ExternalTypes] [ExternalFuns]
/-- This statement is the unchanged Link itself. All publications are actual
successful finish results; neither arbitrary Fields nor a range premise occurs. -/
theorem actual {I : Type} (runs : I → Run) : PV_RunJoin_Link_QueryRange runs := by
  intro i prepared salts p hp hs hf
  rw [PV_RunJoin_FinishContext47.source] at hf
  exact PV_RJQ_FinishQueries.run .S2 (runs i).hash prepared salts _ _ p hf
#print axioms actual
end R1Z.PV_RJQ_QueryRange
