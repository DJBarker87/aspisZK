import R1Z.PV_RDB2C_PV_B2_C_RawWeights251Funs
set_option autoImplicit false
namespace PV_B2_C_MutationStep
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev Out := Array E 1024#usize
abbrev Powers := E × E × E × E × E × E × E
/-- The generated body forwards exactly the array returned by update. -/
theorem body_step (w : host_weights.Weights) (k : Powers) (out : Out)
    (j : Usize) (hj : j < 1024#usize) :
    host_weights.materialize_values_loop.body w k out j = (do
      let x ← host_weights.materialize_cell w k j
      let updated ← Array.update out j x
      ok (cont (updated,Usize.wrapping_add j 1#usize))) := by
  simp only [host_weights.materialize_values_loop.body,hj,if_pos,lift,bind_tc_ok]
theorem body_done (w : host_weights.Weights) (k : Powers) (out : Out)
    (j : Usize) (hj : ¬ j < 1024#usize) :
    host_weights.materialize_values_loop.body w k out j = ok (done out) := by
  simp only [host_weights.materialize_values_loop.body,hj,if_false]
theorem cell_failure (w : host_weights.Weights) (k : Powers) (out : Out)
    (j : Usize) (hj : j < 1024#usize) (e : Error)
    (he : host_weights.materialize_cell w k j = fail e) :
    host_weights.materialize_values_loop.body w k out j = fail e := by
  rw [body_step w k out j hj,he,bind_tc_fail]
theorem cell_divergence (w : host_weights.Weights) (k : Powers) (out : Out)
    (j : Usize) (hj : j < 1024#usize)
    (he : host_weights.materialize_cell w k j = div) :
    host_weights.materialize_values_loop.body w k out j = div := by
  rw [body_step w k out j hj,he,bind_tc_div]
#print axioms body_step
#print axioms body_done
#print axioms cell_failure
#print axioms cell_divergence
end PV_B2_C_MutationStep
