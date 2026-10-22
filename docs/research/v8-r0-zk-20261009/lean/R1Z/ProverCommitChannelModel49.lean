import R1Z.ProverCommitChannelSum49
import Mathlib.Algebra.BigOperators.Fin
/-! The reduced scalar channel is exactly a three-term base-field dot. -/
set_option autoImplicit false
namespace R1Z.ProverCommitChannelModel49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open AspisV8R15.ExactTowerBase
open ProverCommitChannelSum49
open scoped BigOperators

theorem cast_sum (a b : Nat → U32) (n j : Nat) :
    (sum a b n j : M31Exact)=∑ i : Fin n,
      ((a (j+i.val)).val : M31Exact)*((b (j+i.val)).val : M31Exact) := by
  induction n generalizing j with
  | zero => simp only [sum,Nat.cast_zero,Fin.sum_univ_zero]
  | succ n ih =>
    rw [sum,Nat.cast_add,Nat.cast_mul,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem dot3_exact (a b : Nat → U32)
    (ha : ∀ i, i<3 → (a i).val<ProverCommitChannelSum49.P)
    (hb : ∀ i, i<3 → (b i).val<ProverCommitChannelSum49.P) :
    ∃ z : U32, channels.dot3 (ProverCommitM31Array48.array 3#usize a) (ProverCommitM31Array48.array 3#usize b)=ok z ∧
      z.val<ProverCommitChannelSum49.P ∧ (z.val : M31Exact)=
        ∑ i : Fin 3, ((a i.val).val : M31Exact)*((b i.val).val : M31Exact) := by
  obtain ⟨z,hz,hcz,hdz⟩ := dot3_value a b ha hb
  refine ⟨z,hz,hcz,?_⟩
  simpa only [Nat.zero_add] using hdz.trans (cast_sum a b 3 0)

#print axioms cast_sum
#print axioms dot3_exact
end R1Z.ProverCommitChannelModel49
