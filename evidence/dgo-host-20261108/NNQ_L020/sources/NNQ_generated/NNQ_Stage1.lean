import NNQ_StageLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer
attribute [local irreducible] S2W_Outer.first_decoded

theorem stage1_sim (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    Sim (stage1_owned {S with op43 := o} traceEffects program accounts data)
      (stage1_owned S traceEffects program accounts data) := by
  unfold stage1_owned
  simp only [helper_0, helper_3, helper_8, afterstate_op43]
  repeat' first
    | (solve | exact sim_pure _)
    | (solve | apply sim_lift_congr; rfl)
    | (solve | exact first_decoded_sim S o _ _ _ _)
    | (solve | apply sim_perform; exact .same _ (by simp [NotDigest, S2W_Trace.operationId]))
    | with_reducible apply sim_if
    | with_reducible apply sim_bind
    | intro x
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [traceEffects])
    | split
#print axioms stage1_sim
attribute [local irreducible] S2W_Outer.mapError

theorem stage2_sim (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    Sim (stage2_owned {S with op43 := o} traceEffects program accounts data slot)
      (stage2_owned S traceEffects program accounts data slot) := by
  unfold stage2_owned
  simp only [validate_op43, helper_0, AdapterRw.observer, afterstate_op43, statement_size_op43]
  repeat' first
    | (solve | exact sim_pure _)
    | (solve | apply sim_lift_congr; rfl)
    | (solve | exact sim_mapError _)
    | (solve | apply sim_perform; apply CallSim.op11; rfl)
    | (solve | apply sim_perform; exact .same _ (by simp [NotDigest, S2W_Trace.operationId]))
    | with_reducible apply sim_if
    | with_reducible apply sim_bind
    | intro x
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [traceEffects])
    | split
#print axioms stage2_sim
end AspisR1.NNQ_HostDigest
end
