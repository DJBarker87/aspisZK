import FJr_BodyPairMeaning
import SAG_FinalPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_FinalMessage
open Aeneas Aeneas.Std
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (fm : Slice U8) (f : Fin 64 → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f=MultiproofConeCanonical.bytesOf fm.val) :
    (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field fm i.val)=f := by
  have decoded := (SelectedFieldSequenceCodec.decodeWide_eq_some_iff
    (SelectedFieldSequenceCodec.encodeWide f) f).mp (SelectedFieldSequenceCodec.decodeWide_encode f)
  rw [encoded] at decoded
  funext i
  simp only [FJc_InactiveCoefficientsModel.field,decoded.2 i,Option.getD_some]

theorem length (fm : Slice U8) (f : Fin 64 → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f=MultiproofConeCanonical.bytesOf fm.val) :
    fm.val.length=2048 := by
  have len := congrArg List.length encoded
  simpa only [SelectedFieldSequenceCodec.encodeWide_length,MultiproofConeCanonical.bytesOf,List.length_map] using len.symm


#print axioms value
#print axioms length
end AspisR1.FJs_FinalMessage
end
