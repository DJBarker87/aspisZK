import NMG_179_Widths
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMG_179_QueryBounds
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- SAME final_message is exactly the maximum permitted native sampler payload. -/
theorem source (base : Ops) (reserved : Bool) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (proofSize : i.proof.val.length=57607)
 (reached : NHL_PrepareModel.Reaches base reserved i.digest i.proof v) :
 (InstalledPreparation.retainedView v).final_message.val.length≤2048 := by
 have widths := NMG_179_Widths.source base reserved i v proofSize reached
 exact Nat.le_of_eq widths.2.2.2.2.1
#print axioms source
end AspisR1.NMG_179_QueryBounds
end
