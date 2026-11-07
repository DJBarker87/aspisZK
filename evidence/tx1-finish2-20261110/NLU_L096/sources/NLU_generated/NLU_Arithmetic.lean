import NLU_FieldValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Arithmetic
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NLU_FieldLog (Frame Replies)
def code (r : NP6_StdModel.Reservation) (f : Frame) : Result NLU.Q := do
 let product ← (IDa_Deployed.boundaries r).mul f.eta f.terminal
 let partialValue ← (IDa_Deployed.boundaries r).add f.mask product
 (IDa_Deployed.boundaries r).add partialValue f.extra
/-- Complete canonical arithmetic segment at SAME original/intermediate
operands. The three native replies are instantiated internally with the
emitted value laws; none is a successful-child or endpoint premise. -/
theorem source (r : NP6_StdModel.Reservation) (native : NLU_FieldLog.Native)
 (cut : NLU_FieldLog.Cut native) (f : Frame)
 (he : JFv_RoundArithmetic.Canonical f.eta) (ht : JFv_RoundArithmetic.Canonical f.terminal)
 (hm : JFv_RoundArithmetic.Canonical f.mask) (hx : JFv_RoundArithmetic.Canonical f.extra) :
 ∃ replies : Replies,
 code r f=ok replies.total ∧ JFv_RoundArithmetic.Canonical replies.total ∧
 (native f replies).calls=3 ∧
 (∀ i : Fin 3,NLU.cell (native f replies).args i.val i.isLt=NLU_FieldLog.arguments f replies i) ∧
 (native f replies).returned=replies.total ∧
 FIv_NativeValue.decode (FIq_Carriers.toQ replies.total)=
  (FIv_NativeValue.decode (FIq_Carriers.toQ f.mask)+
   FIv_NativeValue.decode (FIq_Carriers.toQ f.eta)*FIv_NativeValue.decode (FIq_Carriers.toQ f.terminal))+
  FIv_NativeValue.decode (FIq_Carriers.toQ f.extra) := by
 obtain ⟨product,mul,hp,vp⟩:=NLU_FieldValues.mul_value r f.eta f.terminal he ht
 obtain ⟨partialValue,add1,hpartial,vpartial⟩:=NLU_FieldValues.add_value r f.mask product hm hp
 obtain ⟨total,add2,hfinal,vfinal⟩:=NLU_FieldValues.add_value r partialValue f.extra hpartial hx
 let replies : Replies:=⟨product,partialValue,total⟩
 have calls:=NLU_FieldLog.complete native cut f replies
 refine ⟨replies,?_,hfinal,calls.1,calls.2.1,calls.2.2,?_⟩
 · simp only [code,mul,add1,add2,bind_tc_ok]
   rfl
 · change FIv_NativeValue.decode (FIq_Carriers.toQ total)=_
   rw [vfinal,vpartial,vp]
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NLU_Arithmetic
end
