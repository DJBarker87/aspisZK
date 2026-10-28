import NDO_JGj_ModulusWord
import NDO_JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ZeroSubtract
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
def source (x : U64) (y : U32) : Result U64 := do
  let p ← UScalar.add x (FJb_WideSum4.wide field.P)
  UScalar.sub p (FJb_WideSum4.wide y)
theorem success (x : U64) (y : U32) (bx : x.val<61*P) (by0 : y.val<P) :
    ∃ out,source x y=ok out := by
  have vp : (FJb_WideSum4.wide field.P).val=P := JGj_ModulusWord.value
  have lim : 62*P<2^64 := by norm_num [P,AspisV8R17.RawReducer.P]
  obtain ⟨withP,rp,vp0⟩ := ExtractedMaskReducerOps.add_success x (FJb_WideSum4.wide field.P) (by rw [vp];omega)
  have safe : (FJb_WideSum4.wide y).val≤withP.val := by rw [FJb_WideSum4.wide_val,vp0,vp];omega
  obtain ⟨out,ro,_⟩ := ExtractedMaskReducerOps.sub_success withP (FJb_WideSum4.wide y) safe
  refine ⟨out,?_⟩
  simp only [source,rp,bind_tc_ok,ro]
#print axioms success
end AspisR1.JGj_ZeroSubtract
end
