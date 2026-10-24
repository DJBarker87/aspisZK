import S6CurrentAdapterModelV1

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
      let r ← ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        p publicInput proof split () none
      AdapterRw.core.result.Result.map_err
        (BuiltinFnOnce AdapterRw.aspis_r1_cost_probe.verifier.Error PE) r ops.op44) := by
  rfl

/-- A mapped error cannot become an inner success even if error conversion fails. -/
theorem error_bind_ne_ok {A E : Type} (m : Result E) (v : A) :
    (do let e ← m; ok (core.result.Result.Err e : core.result.Result A E)) ≠
      ok (core.result.Result.Ok v : core.result.Result A E) := by
  cases m <;> simp [Bind.bind,Aeneas.Std.bind]

/-- Reconcile the scalar length guard with the exact range operator, without
changing the selected proof bytes. -/
@[aesop safe forward]
theorem range_end_of_length (proof selected : Slice U8) (start finish : Usize)
    (length : proof.val.length = finish.val)
    (range : core.slice.index.SliceIndexRangeUsizeSlice.index
      {start := start, «end» := finish} proof = ok selected) :
    core.slice.index.SliceIndexRangeUsizeSlice.index
      {start := start, «end» := Slice.len proof} proof = ok selected := by
  have same : Slice.len proof = finish := UScalar.eq_of_val_eq length
  rw [same]
  exact range

elab "uncase_result" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    for decl in ← Lean.getLCtx do
      let type ← Lean.Meta.whnf decl.type
      if type.isAppOfArity ``core.result.Result 2 ||
          type.isConstOf ``core.convert.Infallible then
        return (← goal.cases decl.fvarId).toList.map (·.mvarId)
    throwError "no result variable"

elab "head_reduce " h:ident : tactic => do
  let id ← Lean.Elab.Tactic.getFVarId h
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let type ← id.getType
    let args := type.getAppArgs
    unless type.isAppOfArity ``Eq 3 do throwError "not equality"
    let lhs ← Lean.Meta.whnfHeadPred args[1]! (fun e => pure (!e.isAppOf ``ite && !e.isAppOf ``dite))
    if lhs == args[1]! then throwError "head unchanged"
    let next ← Lean.Meta.mkEq lhs args[2]!
    return [← goal.changeLocalDecl id next]

attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.require_distinct_accounts AdapterRw.r1_pool_adapter.owned.require_readonly_buffer AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint AdapterRw.r1_pool_adapter.owned.OwnedAccount.data AdapterRw.r1_pool_adapter.owned.require_zero AdapterRw.first_decoded AdapterRw.r1_pool_adapter.owned.validate_asq8

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
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

/-- The actual accepted stage1 retains the SAME decoded statement, raw public
bytes, proof range, verifier arguments and returned checkpoint. -/
theorem stage1_call (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput proofInput statement semantic selected split start finish,
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok proofInput) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok publicInput) ∧
      ops.op47 publicInput = ok (.Ok statement) ∧
      ops.op21 statement = ok (.Ok ()) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofInput {start := start, «end» := finish} = ok selected ∧
      AdapterRw.first_decoded ops semantic publicInput selected split = ok (.Ok checkpoint) ∧
      Slice.len proofInput = finish := by
  unfold AdapterRw.r1_pool_adapter.owned.stage1_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

/-- Full owned stage2 acceptance supplies the exact tx2 call and SAME statement
passed to the emitter. Its authentication body is extracted, not an Ops field. -/
theorem stage2_call (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot =
      ok (.Ok ())) :
    ∃ validated proofAccount checkpointAccount proofInput checkpointInput publicArray selected start finish,
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok validated) ∧
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 6#usize = ok checkpointAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok proofInput) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops checkpointAccount = ok (.Ok checkpointInput) ∧
      ops.op22 validated.statement = ok (.Ok publicArray) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofInput {start := start, «end» := finish} = ok selected ∧
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice publicArray) selected checkpointInput () none = ok (.Ok ()) ∧
      ops.op53 validated.statement = ok (.Ok ()) ∧
      Slice.len proofInput = finish := by
  unfold AdapterRw.r1_pool_adapter.owned.stage2_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])
#print axioms range_end_of_length
#print axioms error_bind_ne_ok
#print axioms bind_success
#print axioms observer_none
#print axioms first_decoded_call
#print axioms stage1_checkpoint_length
#print axioms stage1_call
#print axioms stage2_call
end AspisR1.AdapterRw.Cuts
