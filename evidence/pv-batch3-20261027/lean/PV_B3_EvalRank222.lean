import PV_B3_EvalCounter222
namespace PV_B3_EvalRank222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_222 PV_B3_EvalCounter222
set_option autoImplicit false

theorem increment (i bound : Usize) (h : i.val < bound.val) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  have small : i.val + 1 < Usize.size := by
    have hb : bound.val < Usize.size := by
      simpa only [UScalar.size_UScalarTyUsize] using bound.hSize
    omega
  simp only [Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  change (i.val + 1) % Usize.size = i.val + 1
  exact Nat.mod_eq_of_lt small

def rank (weights : host_multilinear.SparseWeights) (s : State) : Nat :=
  weights.len.val - s.2.val

theorem decreases (column : Slice Q) (weights : host_multilinear.SparseWeights)
    (sum : Q) (i : Usize) (next : State)
    (h : host_multilinear.multilinear_evaluate_qm31_loop.body column weights sum i = ok (cont next)) :
    rank weights next < rank weights (sum, i) := by
  obtain ⟨hi, hn⟩ := body_counter column weights sum i (cont next) h
  unfold rank
  dsimp only
  rw [hn, increment i weights.len hi]
  omega

#print axioms increment
#print axioms rank
#print axioms decreases
end PV_B3_EvalRank222
