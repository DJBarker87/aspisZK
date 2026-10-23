import R1Z.ProverCommitExtra48
import R0P.MaskProtocol
/-! Symbolic two-Horner value equals the model's Libra linear functional. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitExtraMath51
open scoped BigOperators
open AspisR1.ExtractedCurrentQM31Exact (QM31Exact decode)
open R1Z.ProverCommitPrimitive47 R1Z.ProverCommitSubfieldOps47

def polynomial {K : Type} [Semiring K] (q : Nat → K) (offset n : Nat) (x : K) : K :=
  ∑ k ∈ Finset.range n, q (offset+k)*x^k

theorem source_polynomial (q : Nat → Old.Q) (offset n : Nat) (x : QM31Exact) :
    ProverCommitExtra48.polynomial q offset x n=polynomial (fun j => decode (q j)) offset n x := by
  induction n with
  | zero => simp only [ProverCommitExtra48.polynomial,polynomial,Finset.range_zero,Finset.sum_empty]
  | succ n ih => simp only [ProverCommitExtra48.polynomial,ih,polynomial,Finset.sum_range_succ]

def weight {K : Type} [Semiring K] (a b : K) (j : Nat) : K :=
  if j<28 then a^j else if j<56 then b^(j-28) else 0

theorem dot_polynomial {K : Type} [CommSemiring K] (q : Nat → K) (a b : K) :
    (∑ j ∈ Finset.range 1024, weight a b j*q j)=polynomial q 0 28 a+polynomial q 28 28 b := by
  rw [show 1024=56+968 from rfl,Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range 968, weight a b (56+j)*q (56+j))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [weight,if_neg (by omega : ¬56+j<28),if_neg (by omega : ¬56+j<56),zero_mul]
  rw [hzero,add_zero,show 56=28+28 from rfl,Finset.sum_range_add]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j hj
    have h : j<28 := Finset.mem_range.mp hj
    simp only [weight,if_pos h,polynomial,Nat.zero_add]
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro j hj
    have h : j<28 := Finset.mem_range.mp hj
    simp only [weight,if_neg (by omega : ¬28+j<28),if_pos (by omega : 28+j<56),Nat.add_sub_cancel_left]
    exact mul_comm _ _

#print axioms source_polynomial
#print axioms dot_polynomial
end R1Z.ProverCommitExtraMath51
