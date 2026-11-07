import NHS_ViewWidths
import NHS_QueryPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_CallerWidths
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Widths are produced by the fixed-width preparation prefix and original
sourceView; no constructor output or scalar success is a premise. -/
theorem reached (base : Ops) (reserved : Bool) {H : Type}
 (D : aspis_core.digest.Digest32 H) (proof : Slice U8) (v : verifier.View)
 (proofSize : proof.val.length=57607)
 (run : NHL_PrepareModel.Reaches base reserved D proof v) :
 let retained := InstalledPreparation.retainedView v
 retained.variant=.S2 ∧ retained.y1.val.length=928 ∧ retained.round0.val.length=224 ∧
 retained.round1.val.length=224 ∧ retained.final_message.val.length=2048 := by
 obtain ⟨_,_,semantic,y1,_,ySize,view,_⟩ := NHL_PrepareDomain.reached base reserved D proof v proofSize run
 obtain ⟨variant,y1,round0,round1,final⟩ := NHS_ViewWidths.source proof semantic y1 v (by omega) ySize view
 exact ⟨by change InstalledPreparation.retainedVariant v.variant=_;rw [variant];rfl,y1,round0,round1,final⟩

/-- Scalar S1/S2/S3/S6 root widths are within the CLOSED NGT native domain. -/
theorem scalar_bounds (v : AspisR1PublicPreparation.verifier.View)
 (ySize : v.y1.val.length=928) (roundSize : v.round0.val.length=224)
 (bytes : Array U8 32#usize) :
 v.y1.val.length≤2048 ∧ (Array.to_slice bytes).val.length≤2048 ∧
 v.round0.val.length≤2048 ∧
 AspisR1PublicPreparation.PreparedScratchReachability.emptyPayload.val.length≤2048 := by
 have size := bytes.property
 change bytes.val.length=32 at size
 change _ ∧ bytes.val.length≤2048 ∧ _ ∧ 0≤2048
 omega
#print axioms reached
#print axioms scalar_bounds
end AspisR1.NHS_CallerWidths
