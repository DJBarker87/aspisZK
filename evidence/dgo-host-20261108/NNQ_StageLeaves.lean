import NNQ_FirstDecoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result S2W_Trace
theorem sim_if (p : Prop) [Decidable p] {A : Type} (l1 l2 r1 r2 : Code A)
    (ht : p → Sim l1 l2) (hf : ¬ p → Sim r1 r2) :
    Sim (if p then l1 else r1) (if p then l2 else r2) := by
  by_cases h : p
  · simpa only [if_pos h] using ht h
  · simpa only [if_neg h] using hf h

theorem sim_lift_congr {A : Type} (r1 r2 : Result A) (h : r1 = r2) :
    Sim (monadLift r1 : Code A) (monadLift r2) := by
  rw [h]
  exact sim_lift _
#print axioms sim_if
#print axioms sim_lift_congr


variable (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
theorem afterstate_op43 :
    AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES {S with op43 := o} =
    AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES S := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  rfl
theorem statement_size_op43 :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES {S with op43 := o} =
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES S := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
  rfl
#print axioms afterstate_op43
#print axioms statement_size_op43
end AspisR1.NNQ_HostDigest
end
