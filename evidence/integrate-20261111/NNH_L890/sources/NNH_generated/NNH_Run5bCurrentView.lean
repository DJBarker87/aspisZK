import NNH_Run5bCurrentShape
import LIBC_WideView
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCurrentView
open Aeneas Aeneas.Std Result NNH_Libraries NNH_Run5bCurrentShape
open AspisR1CurrentCaller
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem slot (proof semantic y1 : Slice U8) :
 (current m env err r).op5 proof semantic y1 = InstalledPreparation.sourceView proof semantic y1 := rfl

theorem returned (proof semantic y1 : Slice U8) (v : VL.View)
 (width : proof.val.length=57607) (ls : semantic.val.length=13831) (ly : y1.val.length=928)
 (called : LIB_VLib.wideViewValue (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env=.ok v) :
 ∃ native : AspisR1SelectedWideViewV1.verifier.View,
 AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1 = .ok (.Ok native) ∧
 InstalledPreparation.retainedView (InstalledPreparation.selectedView native) = v ∧
 (current m env err r).op5 proof semantic y1 = .ok (.Ok (InstalledPreparation.selectedView native)) := by
 have domain : LIBC_WideView.Domain (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) := by
  simpa only [LIBC_WideView.Domain,LIB_Carriers.bytes,List.length_map] using And.intro width (And.intro ls ly)
 change LIBC_WideView.value (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env=.ok v at called
 have mapped := LIBC_WideView.model_port _ env domain
 simp only [LIBC_Bytes.from_native] at mapped
 rw [called] at mapped
 cases native : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1 with
 | fail e => rw [native] at mapped; cases mapped
 | div => rw [native] at mapped; cases mapped
 | ok reply => cases reply with
  | Err e => rw [native] at mapped; cases mapped
  | Ok out =>
   rw [native] at mapped
   have image : AspisR1SelectedWideViewV1.preparedView out = v := Except.ok.inj (Result.ok.inj mapped)
   refine ⟨out,rfl,?_,?_⟩
   · exact (LIBC_WideView.emitted_copy out).trans image
   · rw [slot]
     unfold InstalledPreparation.sourceView
     rw [native]
     rfl
#print axioms slot
#print axioms returned
end AspisR1.NNH_Run5bCurrentView
end
