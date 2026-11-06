import NIW_AlignFinish
import NIW_AlignOwner
import NIT_FinishArguments
import NIT_FinishSkeleton
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_FinishRoot
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- Negative interface result for the old cut alone. The new payload cut
excludes these altered-payload records by observing every raw-field window. -/
theorem old_new_cut_does_not_identify (p : verifier.Prepared) (alpha z owner : Nat)
 (before after : NewPort) (out : Ref FIo_Install.W)
 (native : cutNewPort p alpha z owner before after (.Ok out)) (expected : FIo_Install.W) :
 ¬ (∀ value : Ref FIo_Install.W,
  cutNewPort p alpha z owner before after (.Ok value) → value.value=expected) := by
 intro identifies
 let left : FIo_Install.W := {out.value with variant:=FIn_WeightsExtract.FInVariant.S1}
 let right : FIo_Install.W := {out.value with variant:=FIn_WeightsExtract.FInVariant.S2}
 have hl := identifies {out with value:=left}
  (NIW_AlignFinish.new_payload_free p alpha z owner before after out left native)
 have hr := identifies {out with value:=right}
  (NIW_AlignFinish.new_payload_free p alpha z owner before after out right native)
 have impossible := congrArg FIn_WeightsExtract.Weights.variant (hl.trans hr.symm)
 cases impossible

/-- The retained hypothesis is the SAME finish-call caller domain. It is not
proved or strengthened by these cuts; no whole-finish native theorem is claimed. -/
#check NIG_FinishInput.Domain
#check NIT_FinishSkeleton.source
#check NIW_AlignOwner.returned
#print axioms old_new_cut_does_not_identify
end AspisR1.NIW_FinishRoot
