import NHF_SegmentedFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_ViewInstalled
open Aeneas Aeneas.Std Result AspisR1CurrentCaller InstalledPreparation

def port (r : core.result.Result AspisR1SelectedWideViewV1.verifier.View
 AspisR1SelectedWideViewV1.verifier.Error) : core.result.Result verifier.View verifier.Error :=
 match r with
 | .Ok v => .Ok (selectedView v)
 | .Err e => .Err (selectedError e)
/-- Complete result at the actual installed current-caller operation, with the
nominal output/error ports retained, not a parallel uninstalled view model. -/
theorem result (proof semantic y1 : Slice U8) (size : 10055 ≤ proof.val.length) :
 sourceView proof semantic y1 = ok (port (NHF_ViewResult.model proof semantic y1 size)) := by
 unfold sourceView
 rw [NHF_ViewResult.result proof semantic y1 size,bind_tc_ok]
 rfl
/-- The sole prepare caller's exact stored length establishes the leaf domain. -/
theorem caller_domain (proof : Slice U8) (size : proof.val.length=57607) :
 10055 ≤ proof.val.length := by omega
#print axioms result
#print axioms caller_domain
end AspisR1.NHF_ViewInstalled
end
