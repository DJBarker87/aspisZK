import AdapterRwModel

set_option autoImplicit false
namespace AspisR1.AdapterRw.Cuts
open Aeneas Aeneas.Std Result AdapterRw
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Statement := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1

/-- Invert outer success without discarding native errors, failure or divergence. -/
theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a) = ok out) : ∃ a, m = ok a ∧ f a = ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The SHIPPED observer body extracts to None; no child hypothesis. -/
theorem observer_none (ops : AdapterRw.Ops) : AdapterRw.observer ops = ok none := rfl

/-- Exact verifier call from the SHIPPED first_decoded body, including None.
This is a per-call extraction fact, not a native effect-frame theorem. -/
theorem first_decoded_call (ops : AdapterRw.Ops)
    (p : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicInput proof : Slice U8) (split : Usize) :
    AdapterRw.first_decoded ops p publicInput proof split = (do
      let r ← ops.op12 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        p publicInput proof split () none
      AdapterRw.core.result.Result.map_err
        (BuiltinFnOnce AdapterRw.aspis_r1_cost_probe.verifier.Error PE) r ops.op49) := by
  rfl

macro "peel_run" h:ident : tactic => `(tactic|
  repeat' first
  | simp only [bind_tc_ok, AdapterRw.core.result.Result.map_err,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame] at $h
  | contradiction
  | split at $h
  | obtain ⟨value, step, $h⟩ := bind_success _ _ _ $h)

/-- A successful whole owned TX1 must return a vector whose length equals the
same checkpoint data inspected before decoding. No child output is fabricated. -/
theorem stage1_checkpoint_length (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ account bytes,
      Slice.index_usize accounts 2#usize = ok account ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops account = ok (.Ok bytes) ∧
      alloc.vec.Vec.len checkpoint = Slice.len bytes := by
  unfold AdapterRw.r1_pool_adapter.owned.stage1_owned at accepted
  peel_run accepted
  all_goals trace_state
  all_goals aesop

#print axioms bind_success
#print axioms observer_none
#print axioms first_decoded_call
#print axioms stage1_checkpoint_length
end AspisR1.AdapterRw.Cuts
