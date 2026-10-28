import R1Z.PV_RDB2C_PV_B2_F_CellFold
set_option autoImplicit false
namespace PV_B2_F_MutationModel
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- Ordered traversal of the remaining output slots. This records every complete
cell result and array update, rather than discarding an iterator restoration. -/
def remaining (w : host_weights.Weights) (k : Powers) : Nat → Usize → Out → Result Out
  | 0, _, out => ok out
  | n+1, j, out => do
    let x ← PV_B2_F_CellFold.ordered w k j
    let out1 ← Array.update out j x
    remaining w k n (Usize.wrapping_add j 1#usize) out1

theorem loop (w : host_weights.Weights) (k : Powers) (out : Out) (j : Usize) :
    host_weights.materialize_values_loop w out k j = remaining w k (1024-j.val) j out := by
  suffices ∀ n (j : Usize) (out : Out), 1024-j.val=n →
    host_weights.materialize_values_loop w out k j = remaining w k n j out from
      this (1024-j.val) j out rfl
  intro n
  induction n with
  | zero =>
    intro j out hn
    have hj : ¬ j < 1024#usize := by scalar_tac
    rw [PV_B2_C_MutationLoop.done w k out j hj]
    rfl
  | succ n ih =>
    intro j out hn
    have hj : j < 1024#usize := by scalar_tac
    have hn1 : 1024-(Usize.wrapping_add j 1#usize).val=n := by
      rw [PV_B2_C_MutationTotal.next_val j hj]
      omega
    rw [PV_B2_C_MutationLoop.step w k out j hj,PV_B2_F_CellFold.source]
    simp only [remaining]
    obtain ⟨x,hx⟩ := PV_B2_D_MaterializeTotal.cell w k j hj
    rw [PV_B2_F_CellFold.source] at hx
    simp only [hx,bind_tc_ok]
    obtain ⟨out1,hu⟩ := PV_B2_C_MutationLoop.update_total out j x hj
    simp only [hu,bind_tc_ok]
    exact ih _ _ hn1

/-- Full copied kernel with ordered-state semantics. No caller success premise. -/
def values (w : host_weights.Weights) (kappa : E) (out : Out) : Result Out := do
  let k ← host_weights.powers7 kappa
  remaining w k 1024 0#usize out

theorem source (w : host_weights.Weights) (kappa : E) (out : Out) :
    host_weights.materialize_values w kappa out = values w kappa out := by
  unfold host_weights.materialize_values values
  obtain ⟨k,hk⟩ := PV_B2_C_Powers7Total.source kappa
  rw [hk,bind_tc_ok,loop]
  rfl
#print axioms loop
#print axioms source
end PV_B2_F_MutationModel
