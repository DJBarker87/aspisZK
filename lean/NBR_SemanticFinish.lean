import NBL_ClaimDomain
set_option autoImplicit false
namespace AspisR1.NBR_SemanticFinish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Invert the SAME complete semantic producer Result, deriving its prefix,
public transcript, challenges and finish execution. No selected successful
finish or independently chosen semantic value is a hypothesis. -/
theorem source (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (call : VerifyPrefix.verify F D pub bytes hash obs=ok (.Ok sem)) :
    ∃ (pre : r1_wire.Prefix) (initial before : r1_wire.SemanticTranscript H)
      (challenges : r1_wire.Challenges),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      r1_semantic.public_transcript D pub hash pre.c1_root=ok (.Ok initial) ∧
      r1_wire.begin D pre initial=ok (.Ok challenges,before) ∧
      F D pub pre before challenges obs=ok (.Ok sem) := by
  unfold VerifyPrefix.verify at call
  obtain ⟨parsed,parse,rest⟩ := NBA_Inactive.bind_success _ _ _ call
  cases parsed with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at rest
    cases rest
  | Ok pre =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark,bind_tc_ok] at rest
    obtain ⟨started,start,rest⟩ := NBA_Inactive.bind_success _ _ _ rest
    cases started with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at rest
      cases rest
    | Ok initial =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
      obtain ⟨pair,begin,rest⟩ := NBA_Inactive.bind_success _ _ _ rest
      rcases pair with ⟨result,before⟩
      simp only [Aeneas.Std.uncurry] at rest
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at rest
        cases rest
      | Ok challenges =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark,bind_tc_ok] at rest
        exact ⟨pre,initial,before,challenges,parse,start,begin,rest⟩

#print axioms source
end AspisR1.NBR_SemanticFinish
