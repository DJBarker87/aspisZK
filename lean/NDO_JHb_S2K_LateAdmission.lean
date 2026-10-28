import RPz7_S2K_AfterstateEncoding

/-! Success inversion through the actual late-public encoder, preserving the
SAME candidate. Child encoders remain opaque; no call success is postulated. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.LateAdmission
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile pool_v1.pair_terminal

elab "s2k_unpair" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    for decl in ← Lean.getLCtx do
      let type ← Lean.Meta.whnf decl.type
      if type.isAppOfArity ``Prod 2 then
        return (← goal.cases decl.fvarId).toList.map (·.mvarId)
    throwError "no product variable"

elab "s2k_uncase" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    for decl in ← Lean.getLCtx do
      let type ← Lean.Meta.whnf decl.type
      if type.isAppOfArity ``core.result.Result 2 ||
          type.isAppOfArity ``core.ops.control_flow.ControlFlow 2 ||
          type.isConstOf ``core.convert.Infallible then
        return (← goal.cases decl.fvarId).toList.map (·.mvarId)
    throwError "no result/control-flow variable"

theorem candidate (s : PoolV1PairLatePublicStatementV1) (before after : Slice U8)
    (h : encode_pool_v1_pair_late_public_statement_v1 s before = ok (.Ok (),after)) :
    ∃ bytes, encode_pool_v1_pair_verified_afterstate_v1 s.candidate_afterstate = ok (.Ok bytes) := by
  unfold encode_pool_v1_pair_late_public_statement_v1 at h
  simp only [Bind.bind, Aeneas.Std.bind, core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at h
  repeat' first
    | (solve | exact ⟨_,by assumption⟩)
    | (solve | exact ⟨_,rfl⟩)
    | (solve | cases h)
    | (dsimp only [Aeneas.Std.uncurry] at h)
    | (s2k_unpair <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (s2k_uncase <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (split at h)

theorem validated (s : PoolV1PairLatePublicStatementV1) (before after : Slice U8)
    (h : encode_pool_v1_pair_late_public_statement_v1 s before = ok (.Ok (),after)) :
    validate_verified_afterstate s.candidate_afterstate = ok (.Ok ()) := by
  obtain ⟨bytes,run⟩ := candidate s before after h
  have status := AfterstateStatus.status_exact s.candidate_afterstate
  rw [run] at status
  exact status.symm

theorem payload (s : PoolV1PairLatePublicStatementV1) (before after : Slice U8)
    (h : encode_pool_v1_pair_late_public_statement_v1 s before = ok (.Ok (),after)) :
    encode_pool_v1_pair_verified_afterstate_v1 s.candidate_afterstate =
      ok (.Ok (AfterstateEncoding.bytes s.candidate_afterstate)) :=
  AfterstateEncoding.encode_exact _ (validated s before after h)

#print axioms candidate
#print axioms validated
#print axioms payload
end AspisR1.S2K.LateAdmission
