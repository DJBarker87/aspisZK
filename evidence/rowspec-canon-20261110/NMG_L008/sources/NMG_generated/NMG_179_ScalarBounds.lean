import NMG_179_Widths
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMG_179_ScalarBounds
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Every fixed payload bound available at this reached source call, at the
SAME view. This supplies no successful digest/Block or scalar observation. -/
theorem source (base : Ops) (reserved : Bool) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (proofSize : i.proof.val.length=57607)
 (reached : NHL_PrepareModel.Reaches base reserved i.digest i.proof v)
 (bytes : Array U8 32#usize) :
 let retained := InstalledPreparation.retainedView v
 retained.y1.val.length≤2048 ∧ (Array.to_slice bytes).val.length≤2048 ∧
 retained.round0.val.length≤2048 ∧
 AspisR1PublicPreparation.PreparedScratchReachability.emptyPayload.val.length≤2048 := by
 have widths := NMG_179_Widths.source base reserved i v proofSize reached
 exact NHS_CallerWidths.scalar_bounds (InstalledPreparation.retainedView v) widths.2.1 widths.2.2.1 bytes
#print axioms source
end AspisR1.NMG_179_ScalarBounds
end
