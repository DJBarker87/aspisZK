import NHY_ZeroStep
set_option autoImplicit false
namespace NHY_EqualStep
open Aeneas Aeneas.Std Result

theorem terminal (b v : Slice U8) (i : Usize) (bound : b.val.length ≤ i.val) :
    NCX_Reference.equal_loop.body b v i=ok (.done none) := by
  have h : ¬i<Slice.len b := by scalar_tac
  simp only [NCX_Reference.equal_loop.body,h,ite_false]

theorem step (b v : Slice U8) (i : Usize) (cap : b.val.length ≤ 768)
    (length : b.val.length=v.val.length) (bound : i.val < b.val.length) :
    ∃ next : Usize, next.val=i.val+1 ∧
      NCX_Reference.equal_loop.body b v i=
        if NHY_ZeroStep.byte b i.val ≠ NHY_ZeroStep.byte v i.val
        then ok (.done (some false)) else ok (.cont next) := by
  obtain ⟨next,advance,value⟩ := NHY_ZeroLoop.advance i (by omega)
  refine ⟨next,value,?_⟩
  have h : i<Slice.len b := by scalar_tac
  simp only [NCX_Reference.equal_loop.body,h,ite_true,NHY_ZeroStep.read b i bound,
    NHY_ZeroStep.read v i (by omega),bind_tc_ok,advance]
  split <;> simp_all

#print axioms terminal
#print axioms step
end NHY_EqualStep
