import S2K_AfterstateEncoding

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
    | (solve | cases h)
    | (with_unfolding_all dsimp only at h)
    | s2k_unpair
    | (split at h)

#print axioms candidate
end AspisR1.S2K.LateAdmission
