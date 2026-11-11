import PIN2_S1SemanticCodeVerifyV1
import RPz7_S1SemanticCodeVerifyExactV1
import PIN2_S1SemanticCodePublicTranscriptExactV1
/-! PIN2 W7 (2026-11-11), coordinator option L2: erasure of the PIN2 lifted verifier
`verifyPIN2` against the PIN2 translator constant
`AspisR1PublicPreparationPIN2.VerifyPrefix.verify` (W8, PIN2_NEWGATE_verifyprefix), with the
frozen finish model seen through the copies (`finishObs`, which passes the observer through).
The proof goes through `PIN2W7_PrefixGlue.parseAccepted_eq`, `PIN2W7_PrefixGlue.begin_eq`, the
PIN2 `publicTranscript_erasure` (lift of the PIN2 public_transcript, PIN2W7_lift.py) and the
release `begin_erasure`/`finish_erasure`.  The lifted digest event carries
`PIN2W7_PrefixGlue.digestBack D` (the Code monad is typed over the frozen Digest32);
`erase_digest` gives `D.digest` by rfl. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open PIN2W7_PrefixGlue (rmap cres bind_rmap rmap_bind bind_congr')

/-- The frozen finish model through the copies, passing the observer through. -/
def finishObs (F : AspisR1PublicPreparation.VerifyPrefix.Finish) : AspisR1PublicPreparationPIN2.VerifyPrefix.Finish :=
  fun D p pre t ch obs => do
    let r ← F (PIN2W7_PrefixGlue.digestBack D) (PIN2W7_PrefixGlue.fromPIN2 p) (PIN2W7_PrefixGlue.prefixBack pre)
      (PIN2W7_PrefixGlue.transcriptBack t) (PIN2W7_PrefixGlue.challengesBack ch) obs
    ok (cres PIN2W7_PrefixGlue.sem PIN2W7_PrefixGlue.error r)

theorem publicTranscriptPIN2_erasure {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    erase (publicTranscriptPIN2 D pub hash root) =
      rmap (cres PIN2W7_PrefixGlue.transcriptBack PIN2W7_PrefixGlue.errorBack)
        (AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
          (PreparationBinding.toPIN2 pub) hash root) := by
  unfold publicTranscriptPIN2
  rw [erase_bind, AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript_erasure]
  cases AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
    (PreparationBinding.toPIN2 pub) hash root <;> rfl

theorem verifyPIN2_erasure (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    erase (verifyPIN2 (finish R B) D pub bytes hash obs) =
      rmap (cres PIN2W7_PrefixGlue.semBack PIN2W7_PrefixGlue.errorBack)
        (AspisR1PublicPreparationPIN2.VerifyPrefix.verify (finishObs (FinishModel.finish R B))
          (PIN2W7_TranscriptCopy.digest D) (PreparationBinding.toPIN2 pub) bytes hash obs) := by
  unfold verifyPIN2 AspisR1PublicPreparationPIN2.VerifyPrefix.verify
  rw [erase_bind, erase_lift, PIN2W7_PrefixGlue.parseAccepted_eq, bind_rmap, rmap_bind]
  apply bind_congr'; intro r
  cases r with
  | Err e =>
    simp only [erase_bind, erase_lift, cres, Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
    cases e <;> rfl
  | Ok p =>
    simp only [erase_bind, erase_lift, cres, Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    rw [rmap_bind]; apply bind_congr'; intro u
    rw [publicTranscriptPIN2_erasure, bind_rmap, rmap_bind]; apply bind_congr'; intro x
    cases x with
    | Err e =>
      simp only [erase_bind, erase_lift, cres, Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
      cases e <;> rfl
    | Ok t' =>
      obtain ⟨t, rfl⟩ : ∃ t, t' = PIN2W7_TranscriptCopy.transcript t := ⟨PIN2W7_PrefixGlue.transcriptBack t', rfl⟩
      simp only [erase_bind, erase_lift, cres, Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, PIN2W7_PrefixGlue.transcript_round]
      rw [begin_erasure, rmap_bind, PIN2W7_PrefixGlue.begin_eq, bind_rmap]
      apply bind_congr'; rintro ⟨r2, t1⟩
      cases r2 with
      | Err e =>
        simp only [cres, Aeneas.Std.uncurry, erase_lift, Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
          Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
        cases e <;> rfl
      | Ok c =>
        simp only [cres, Aeneas.Std.uncurry, erase_bind, erase_lift, Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        rw [rmap_bind]; apply bind_congr'; intro u'
        rw [finish_erasure]
        unfold finishObs
        simp only [PIN2W7_PrefixGlue.digest_round, PIN2W7_PrefixGlue.fromPIN2_round, PIN2W7_PrefixGlue.prefix_round,
          PIN2W7_PrefixGlue.transcript_round, PIN2W7_PrefixGlue.challenges_round]
        cases FinishModel.finish R B D pub p t1 c obs with
        | ok r =>
          cases r <;> simp only [bind_tc_ok, rmap, cres, PIN2W7_PrefixGlue.sem_round, PIN2W7_PrefixGlue.error_round]
        | fail e => rfl
        | div => rfl
/-- With the observer `none` (the installed semantic leaf), `finishObs` and the glue's
`PIN2W7_PrefixGlue.finish` give the same PIN2 prefix run. -/
theorem verify_finishObs_none (F : AspisR1PublicPreparation.VerifyPrefix.Finish) {H : Type}
    (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    AspisR1PublicPreparationPIN2.VerifyPrefix.verify (finishObs F) D pub bytes hash none =
      AspisR1PublicPreparationPIN2.VerifyPrefix.verify (PIN2W7_PrefixGlue.finish F) D pub bytes hash none := by
  have same : ∀ {H' : Type} (D' : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H') p pre t ch,
      finishObs F D' p pre t ch none = PIN2W7_PrefixGlue.finish F D' p pre t ch none := by
    intro H' D' p pre t ch
    unfold finishObs PIN2W7_PrefixGlue.finish
    apply bind_congr'
    intro r
    cases r <;> rfl
  unfold AspisR1PublicPreparationPIN2.VerifyPrefix.verify
  simp only [same]

#print axioms publicTranscriptPIN2_erasure
#print axioms verifyPIN2_erasure
#print axioms verify_finishObs_none
end AspisR1PublicPreparation.S1SemanticCode
