import R1Z.PV_RDB2C_PV_B2_C_MutationLoop
set_option autoImplicit false
namespace PV_B2_C_MutationTotal
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- A local proof obligation for cells, not an added privacy trust item. -/
def CellsTotal (w : host_weights.Weights) (k : Powers) : Prop :=
  ∀ j : Usize, j < 1024#usize → ∃ x, host_weights.materialize_cell w k j = ok x

theorem next_val (j : Usize) (hj : j < 1024#usize) :
    (Usize.wrapping_add j 1#usize).val = j.val+1 := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt]
  · rfl
  · have hsize : (1025#usize).val < UScalar.size .Usize := by
      simpa only [UScalar.val,UScalar.size,UScalarTy.numBits] using (1025#usize).bv.isLt
    have hle : j.val + (1#usize).val ≤ (1025#usize).val := by scalar_tac
    exact lt_of_le_of_lt hle hsize

/-- Finite induction on remaining indices; never normalize the 1024-cell loop. -/
theorem loop_total (w : host_weights.Weights) (k : Powers) (hc : CellsTotal w k)
    (out : Out) (j : Usize) :
    ∃ updated, host_weights.materialize_values_loop w out k j = ok updated := by
  suffices ∀ n (j : Usize) (out : Out), 1024-j.val = n →
      ∃ updated, host_weights.materialize_values_loop w out k j = ok updated from
    this (1024-j.val) j out rfl
  intro n
  induction n with
  | zero =>
    intro j out hn
    have hj : ¬ j < 1024#usize := by scalar_tac
    exact ⟨out,PV_B2_C_MutationLoop.done w k out j hj⟩
  | succ n ih =>
    intro j out hn
    have hj : j < 1024#usize := by scalar_tac
    obtain ⟨x,hx⟩ := hc j hj
    obtain ⟨out1,hu⟩ := PV_B2_C_MutationLoop.update_total out j x hj
    have hn1 : 1024-(Usize.wrapping_add j 1#usize).val = n := by
      rw [next_val j hj]
      omega
    obtain ⟨out2,ho⟩ := ih (Usize.wrapping_add j 1#usize) out1 hn1
    exact ⟨out2,by rw [PV_B2_C_MutationLoop.step w k out j hj,hx,bind_tc_ok,hu,bind_tc_ok,ho]⟩
#print axioms CellsTotal
#print axioms next_val
#print axioms loop_total
end PV_B2_C_MutationTotal
