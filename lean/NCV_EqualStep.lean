import NCV_ZeroStep
set_option autoImplicit false
namespace NCV_EqualStep
open Aeneas Aeneas.Std Result

theorem terminal (b v : Slice U8) (i : Usize) (bound : b.val.length ≤ i.val) :
    NCV_Reference.equal_loop.body b v i=ok (.done none) := by
  have h : ¬i<Slice.len b := by scalar_tac
  simp only [NCV_Reference.equal_loop.body,h,ite_false]

theorem step (b v : Slice U8) (i : Usize) (cap : b.val.length ≤ 768)
    (length : b.val.length=v.val.length) (bound : i.val < b.val.length) :
    ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.equal_loop.body b v i=
        if NCV_ZeroStep.byte b i.val ≠ NCV_ZeroStep.byte v i.val
        then ok (.done (some false)) else ok (.cont next) := by
  obtain ⟨next,advance,value⟩ := NCV_Loop.advance i (by omega)
  refine ⟨next,value,?_⟩
  have h : i<Slice.len b := by scalar_tac
  simp only [NCV_Reference.equal_loop.body,h,ite_true,NCV_ZeroStep.read b i bound,
    NCV_ZeroStep.read v i (by omega),bind_tc_ok,advance]
  split <;> simp_all

#print axioms terminal
#print axioms step
end NCV_EqualStep
