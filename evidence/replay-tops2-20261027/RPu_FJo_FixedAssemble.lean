import R1FixedWidthDecoder
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.FJo_FixedAssemble
/-- Assemble a strict decoder from the actual indexed successful subreads. -/
theorem value {B A : Type} (d : List B → Option A) (k n : Nat) (bytes : List B)
    (size : bytes.length=k*n)
    (reads : ∀ j : Fin n, ∃ x,d ((bytes.drop (k*j.val)).take k)=some x) :
    ∃ xs, FixedWidthDecoder.decode d k n bytes=some xs := by
  induction n generalizing bytes with
  | zero =>
    refine ⟨Fin.elim0,?_⟩
    simp only [FixedWidthDecoder.decode,show bytes.length=0 by omega,ite_true]
  | succ n ih =>
    obtain ⟨x,hx⟩ := reads 0
    have head : d (bytes.take k)=some x := by simpa only [Fin.val_zero,Nat.mul_zero,List.drop_zero] using hx
    obtain ⟨tail,ht⟩ := ih (bytes.drop k) (by simp only [List.length_drop,size,Nat.mul_add,Nat.mul_one];omega) (by
      intro j
      obtain ⟨v,hv⟩ := reads j.succ
      refine ⟨v,?_⟩
      simpa only [List.drop_drop,Fin.val_succ,Nat.mul_add,Nat.mul_one,Nat.add_comm] using hv)
    refine ⟨Fin.cons x tail,?_⟩
    simp only [FixedWidthDecoder.decode,head,ht,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
#print axioms value
end AspisR1.FJo_FixedAssemble
