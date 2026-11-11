import PIN2_NEWGATE_r1_semantic
import PIN2_NHG_Final

/-! PIN2 W3b (2026-11-11). Final PIN2 forms of `NHG_PublicCarrier.same_execution`,
`new_carrier` and `begin_carrier`, against Stream C's PIN2 emission of
`r1_semantic::public_transcript` and `r1_wire::SemanticTranscript::new`
(`PIN2_NEWGATE_r1_semantic`, source sha b5ff0038fb96…), which calls the PIN2
`public_bytes` of `PIN2_NEWGATE_r0`.  Statements as in the release, with the
length bound ≤ 1524 (was ≤ 1455). The premise is the actual call's result. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PIN2_NHG_PublicCarrier
open PIN2_PublicBytesRefinement (NewPublic)

abbrev Digest32 := AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32
abbrev Transcript := AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript

/-- The state carrier belongs to the SAME successful public producer. -/
theorem same_execution {H : Type} (D : Digest32 H) (q : NewPublic) (hash : H)
    (root : Array U8 32#usize) (t : Transcript H)
    (call : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D q hash root = ok (.Ok t)) :
    ∃ bytes, AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
        ok (.Ok bytes) ∧ bytes.val.length ≤ 1524 ∧
      AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) root =
        ok (.Ok t) := by
  unfold AspisR1PublicPreparationPIN2.r1_semantic.public_transcript at call
  cases produced : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q with
  | fail e => simp only [produced, bind_tc_fail] at call; cases call
  | div => simp only [produced, bind_tc_div] at call; cases call
  | ok result =>
    cases result with
    | Err e =>
      simp only [produced, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
        AspisR1PublicPreparationPIN2.r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at call
      cases call
    | Ok bytes =>
      simp only [produced, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch] at call
      exact ⟨bytes, rfl, PIN2_NHG_Final.returned q bytes produced, call⟩

theorem new_carrier {H : Type} (D : Digest32 H) (hash : H) (bytes : Slice U8)
    (root : Array U8 32#usize) (t : Transcript H)
    (call : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new D hash bytes root = ok (.Ok t)) :
    t.hash = hash ∧ t.next_row = 0#u8 := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new at call
  cases converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes) with
  | fail e => simp only [converted, bind_tc_fail] at call; cases call
  | div => simp only [converted, bind_tc_div] at call; cases call
  | ok result =>
    cases result with
    | Err e =>
      simp only [converted, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
        AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at call
      cases call
    | Ok n =>
      simp only [converted, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, lift] at call
      generalize hd : D.digest hash _ = digested at call
      cases digested with
      | fail e => simp only [bind_tc_fail] at call; cases call
      | div => simp only [bind_tc_div] at call; cases call
      | ok state =>
        simp only [bind_tc_ok] at call
        cases call
        exact ⟨rfl, rfl⟩

theorem begin_carrier {H : Type} (D : Digest32 H) (q : NewPublic) (hash : H)
    (root : Array U8 32#usize) (t : Transcript H)
    (call : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D q hash root = ok (.Ok t)) :
    t.hash = hash ∧ t.next_row = 0#u8 := by
  obtain ⟨bytes, _, _, source⟩ := same_execution D q hash root t call
  exact new_carrier D hash _ root t source

#print axioms same_execution
#print axioms new_carrier
#print axioms begin_carrier
end AspisR1.PIN2_NHG_PublicCarrier
