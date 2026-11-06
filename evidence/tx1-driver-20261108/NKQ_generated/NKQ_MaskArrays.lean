import NKQ_FromFnIndices
import NKQ_MaskLowStep
import NKQ_MaskHighStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_MaskArrays
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NKQ_ArrayWindows
abbrev Q := aspis_core.field.QM31
abbrev Claims := NKQ_MaskLowStep.Claims

def lowValue (c : Claims) (i : Usize) : Q :=
 if h:i.val<16 then NKQ_MaskLowStep.lowAt c i h else aspis_core.field.QM31.ZERO
def highValue (c : Claims) (i : Usize) : Q :=
 if h:i.val<10 then NKQ_MaskHighStep.highAt c i h else aspis_core.field.QM31.ZERO

def lowArray (c : Claims) : Array Q 16#usize :=
 ⟨(OraclePortStdBuilder.indices 16#usize).map (lowValue c),by simp [NKQ_FromFnIndices.length]⟩
def highArray (c : Claims) : Array Q 10#usize :=
 ⟨(OraclePortStdBuilder.indices 10#usize).map (highValue c),by simp [NKQ_FromFnIndices.length]⟩

theorem low_source (reservation : NP6_StdModel.Reservation) {H : Type}
 (D : aspis_core.Digest32 H) (c : Claims) :
 (IDa_Deployed.boundaries reservation).fromFn 16#usize (FinishModel.closureFn9 D) c=ok (lowArray c) := by
 apply NKQ_FromFnIndices.total
 intro i inside
 have bound : i.val<16 := by simpa using inside
 simpa only [lowValue,dif_pos bound] using NKQ_MaskLowStep.step D c i bound

theorem high_source (reservation : NP6_StdModel.Reservation) {H : Type}
 (D : aspis_core.Digest32 H) (c : Claims) :
 (IDa_Deployed.boundaries reservation).fromFn 10#usize (FinishModel.closureFn5 D) c=ok (highArray c) := by
 apply NKQ_FromFnIndices.total
 intro i inside
 have bound : i.val<10 := by simpa using inside
 simpa only [highValue,dif_pos bound] using NKQ_MaskHighStep.step D c i bound
#print axioms low_source
#print axioms high_source
end AspisR1.NKQ_MaskArrays
end
