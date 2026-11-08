import NNV_ViewInverse
import NNH_Run5bCurrentView
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareView
open Aeneas Aeneas.Std Result NNH_Libraries AspisR1CurrentCaller

theorem returned (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof semantic y1 : Slice U8) (v : VL.View)
 (width : proof.val.length=57607) (ls : semantic.val.length=13831) (ly : y1.val.length=928)
 (called : LIB_VLib.wideViewValue (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env=.ok v) :
 (NNH_Run5bCurrentShape.current m env err r).op5 proof semantic y1 = .ok (.Ok (NNV_PreparedInputs.view v)) := by
 obtain ⟨native,_,same,run⟩ := NNH_Run5bCurrentView.returned m env err r proof semantic y1 v width ls ly called
 have image := congrArg NNV_PreparedInputs.view same
 rw [NNV_ViewInverse.source] at image
 exact run.trans (congrArg (fun x => Result.ok (core.result.Result.Ok x)) image)
#print axioms returned
end AspisR1.NNV_PrepareView
end
