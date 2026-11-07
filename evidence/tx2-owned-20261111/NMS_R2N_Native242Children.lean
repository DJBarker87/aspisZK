import NMS_R2N_242Code
import NMS_R2N_GetterMeaning
import NMS_R2N_ScanSites
import NMS_R2N_ReconstructSites
import NMS_RequestModels
import NHJ_IdPacket
set_option autoImplicit false
noncomputable section
namespace NMS_R2N_Native242Children
open Aeneas Aeneas.Std AdapterRw
/-- Proposed fixed interpretations of native/CLOSED children. Their full
site/observation installation and RSL carrier links remain separate obligations;
this definition does not itself establish a native bridge. No arbitrary Ops/Run dictionary
is retained here: Std first/from_array, CLOSED163/158/156/220/226/224 and the
fresh emitted getter with the retained std clone/allocator interpretation.
`devnet` is the compile-feature identifier choice, not an instruction input. -/
def children (devnet : Bool) : NMS_Effect242.Effects RSL.Spec := {
 op9 := fun a => RSL.Spec.pure a.val.head?
 op17 := fun n => NMS_R2N_Interpreted.liftResult (NMS_RequestModels.outputLane n)
 op20 := fun p => NMS_R2N_Interpreted.liftResult (NMS_RequestModels.nullifier p)
 op23 := fun d => NMS_R2N_Interpreted.liftResult (AspisR1.NFY_JHd_RequestNative.decode d)
 op37 := fun p => RSL.Spec.pure p
 op45 := RSL.Spec.pure (NHJ_IdPacket.pool devnet)
 op51 := NMS_R2N_ScanSites.interpreted
 op52 := NMS_R2N_ReconstructSites.meaning
 data := NMS_R2N_GetterMeaning.meaning
}

/-- Only the still-OPEN233 occurrence remains variable in the interpreted
fresh parent. All other child models are fixed above at their original calls. -/
def meaning (devnet : Bool) (authenticate : NMS_Effect242.AuthCall RSL.Spec) :=
 NMS_R2N_242Code.body (children devnet) authenticate
end NMS_R2N_Native242Children
