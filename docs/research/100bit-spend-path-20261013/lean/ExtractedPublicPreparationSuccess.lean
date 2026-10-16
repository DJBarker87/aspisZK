import AspisR1PublicPreparation.Funs

/-! Properties of the two actual emitted preparation helpers. The serializer
witness is derived from helper success. No outer caller execution, Rust/backend
preservation, account or digest semantics is assumed or established here. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.PreparationSuccess
open pool_v1.pair_forest_terminal pool_v1.pair_forest_semantic_terminal.r0

/-- The actual transfer selector borrows precisely its own transition/public. -/
theorem semantic_public_transfer
    (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    PoolV1PairForestTerminalStatementV1.semantic_public (.PrivateTransfer c p) =
      ok (Public.Transfer p c.lane_transition) := rfl

/-- The actual withdrawal selector has the same fixed transition binding. -/
theorem semantic_public_withdrawal
    (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    PoolV1PairForestTerminalStatementV1.semantic_public (.Withdrawal c p) =
      ok (Public.Withdrawal p c.lane_transition) := rfl

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Same public, same serialized bytes, same hash value, same C1 root and same
returned transcript. Inner Err and outer fail/div cannot produce this success. -/
theorem public_transcript_success
    {H : Type} (D : aspis_core.Digest32 H) (p : Public) (hash : H)
    (c1 : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (h : r1_semantic.public_transcript D p hash c1 = ok (.Ok out)) :
    ∃ bytes : alloc.vec.Vec U8,
      Public.public_bytes p = ok (.Ok bytes) ∧
      r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) c1 =
        ok (.Ok out) := by
  unfold r1_semantic.public_transcript at h
  obtain ⟨r, hr, h⟩ := bind_success (Public.public_bytes p) _ _ h
  cases r with
  | Ok bytes =>
    refine ⟨bytes, hr, ?_⟩
    simpa only [core.result.Result.map_err,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] using h
  | Err e =>
    simp only [core.result.Result.map_err,
      r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
      r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok] at h
    cases h

#print axioms semantic_public_transfer
#print axioms semantic_public_withdrawal
#print axioms public_transcript_success
end AspisR1PublicPreparation.PreparationSuccess
