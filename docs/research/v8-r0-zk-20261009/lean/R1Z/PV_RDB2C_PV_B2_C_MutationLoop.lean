import R1Z.PV_RDB2C_PV_B2_C_MutationStep
set_option autoImplicit false
namespace PV_B2_C_MutationLoop
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1 PV_B2_C_MutationStep

theorem update_total (out : Out) (j : Usize) (x : E) (hj : j < 1024#usize) :
    ∃ updated, Array.update out j x = ok updated := by
  obtain ⟨updated,he,_⟩ := WP.spec_imp_exists (Array.update_spec out j x (by
    change j.val < out.val.length
    rw [out.property]
    scalar_tac))
  exact ⟨updated,he⟩

theorem step (w : host_weights.Weights) (k : Powers) (out : Out)
    (j : Usize) (hj : j < 1024#usize) :
    host_weights.materialize_values_loop w out k j = (do
      let x ← host_weights.materialize_cell w k j
      let updated ← Array.update out j x
      host_weights.materialize_values_loop w updated k (Usize.wrapping_add j 1#usize)) := by
  unfold host_weights.materialize_values_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [body_step w k out j hj]
  cases hc : host_weights.materialize_cell w k j with
  | ok x =>
    simp only [hc,bind_tc_ok]
    cases hu : Array.update out j x <;> rfl
  | fail e => rfl
  | div => rfl

theorem done (w : host_weights.Weights) (k : Powers) (out : Out)
    (j : Usize) (hj : ¬ j < 1024#usize) :
    host_weights.materialize_values_loop w out k j = ok out := by
  unfold host_weights.materialize_values_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [body_done w k out j hj,bind_tc_ok]

#print axioms update_total
#print axioms step
#print axioms done
end PV_B2_C_MutationLoop
