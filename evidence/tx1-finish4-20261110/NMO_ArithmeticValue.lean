import NLU_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ArithmeticValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NLU_FieldLog (Frame Replies)
/-- Model-side value composition needs no native operation dictionary or
native scalar-log premise. All three calls are instantiated internally. This
is weaker in hypotheses than the value projection of NLU_Arithmetic.source,
but does not assert native call logging or a TX1:136 row. -/
theorem source (reservation : NP6_StdModel.Reservation) (f : Frame)
 (he : JFv_RoundArithmetic.Canonical f.eta) (ht : JFv_RoundArithmetic.Canonical f.terminal)
 (hm : JFv_RoundArithmetic.Canonical f.mask) (hx : JFv_RoundArithmetic.Canonical f.extra) :
 ∃ replies : Replies,NLU_Arithmetic.code reservation f=ok replies.total ∧
 JFv_RoundArithmetic.Canonical replies.product ∧ JFv_RoundArithmetic.Canonical replies.partialValue ∧
 JFv_RoundArithmetic.Canonical replies.total ∧
 FIv_NativeValue.decode (FIq_Carriers.toQ replies.total)=
  (FIv_NativeValue.decode (FIq_Carriers.toQ f.mask)+
   FIv_NativeValue.decode (FIq_Carriers.toQ f.eta)*FIv_NativeValue.decode (FIq_Carriers.toQ f.terminal))+
  FIv_NativeValue.decode (FIq_Carriers.toQ f.extra) := by
 obtain ⟨product,mul,hp,vp⟩:=NLU_FieldValues.mul_value reservation f.eta f.terminal he ht
 obtain ⟨partialValue,add1,hpartial,vpartial⟩:=NLU_FieldValues.add_value reservation f.mask product hm hp
 obtain ⟨total,add2,hfinal,vfinal⟩:=NLU_FieldValues.add_value reservation partialValue f.extra hpartial hx
 let replies : Replies:=⟨product,partialValue,total⟩
 refine ⟨replies,?_,hp,hpartial,hfinal,?_⟩
 · simp only [NLU_Arithmetic.code,mul,add1,add2,bind_tc_ok]
   rfl
 · change FIv_NativeValue.decode (FIq_Carriers.toQ total)=_
   rw [vfinal,vpartial,vp]
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NMO_ArithmeticValue
end
