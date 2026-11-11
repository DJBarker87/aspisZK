import RPz7_S1SemanticCarrierV1
import RPz7_S1SemanticVerifyReachabilityV1
import RPz7_S1SemanticRootCopyV1
import PIN2_S1SemanticVerifyReachability
import PIN2W7_PrefixGlue
/-! PIN2 W7 (2026-11-11).  The semantic leaf is now W8's PIN2 emission
`AspisR1PublicPreparationPIN2.VerifyPrefix.verify` (PIN2_NEWGATE_verifyprefix) applied to
the field copies of the frozen arguments (`PIN2W7_TranscriptCopy.digest`, W3c's `toPIN2`),
with the frozen finish model passed through `PIN2W7_PrefixGlue.finish` and the result
copied back.  Statement changes: `verify`'s body (definition); `verify_return` now names
the PIN2 `VerifyPrefix.verify` (only change); `verify_roots` changes ONLY its public-init
conjunct, to the PIN2 `public_transcript` on the copies; every other conjunct and every
binder keeps its frozen type.  `verify_roots` uses `PIN2W7_PrefixGlue.parseAccepted_agree`
and `begin_agree` (proved by unfolding both emissions). -/
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.S1SemanticInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open S1SemanticCarrier

/-- Full observed-verifier prefix and finish source bodies, on release None.
All error variants and ambient fail/div are retained through full carriers.
R/B remain explicit semantic leaves; this is not a native source adoption. -/
def verify (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) : Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error) := do
  let result ← AspisR1PublicPreparationPIN2.VerifyPrefix.verify
    (AspisR1PublicPreparation.PIN2W7_PrefixGlue.finish
      (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B)))
    (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest (retainedDigest D))
    (AspisR1PublicPreparation.PreparationBinding.toPIN2 (FirstComposition.toRetainedPublic pub)) bytes hash none
  ok (match result with
    | .Ok sem => .Ok (currentSem (AspisR1PublicPreparation.PIN2W7_PrefixGlue.semBack sem))
    | .Err error => .Err (currentWireError (AspisR1PublicPreparation.PIN2W7_PrefixGlue.errorBack error)))

def install (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Ops :=
  {ops with op9:=fun {H} D pub bytes hash obs =>
    match obs with | none => verify R B D pub bytes hash | some observe => ops.op9 D pub bytes hash (some observe)}

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (success : (m >>= k)=ok out) : ∃ value,m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,success⟩
  | fail error => cases success
  | div => cases success

/-- SAME semantic source return and every field, never an independent
successful prefix/finish call or a replacement semantic object. -/
theorem verify_return (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (success : verify R B D pub bytes hash=ok (.Ok sem)) :
    AspisR1PublicPreparationPIN2.VerifyPrefix.verify
      (AspisR1PublicPreparation.PIN2W7_PrefixGlue.finish
        (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B)))
      (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest (retainedDigest D))
      (AspisR1PublicPreparation.PreparationBinding.toPIN2 (FirstComposition.toRetainedPublic pub)) bytes hash none=
        ok (.Ok (AspisR1PublicPreparation.PIN2W7_PrefixGlue.sem (retainedSem sem))) := by
  unfold verify at success
  obtain ⟨result,source,returned⟩ := bind_success _ _ _ success
  cases result with
  | Err error => cases returned
  | Ok original =>
    have same : currentSem (AspisR1PublicPreparation.PIN2W7_PrefixGlue.semBack original)=sem :=
      core.result.Result.Ok.inj (Result.ok.inj returned)
    rw [←same,semantic_round,AspisR1PublicPreparation.PIN2W7_PrefixGlue.sem_back]
    exact source

/-- Concrete semantic leaf returns source-derived roots. The parser, public
transcript, begin, finish, row payload and copy all belong to this ONE call. -/
theorem verify_roots (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (success : verify R B D pub bytes hash=ok (.Ok sem)) :
    ∃ (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (initial after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
      (payload : Slice U8) (root2 : Array U8 32#usize),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest (retainedDigest D))
        (AspisR1PublicPreparation.PreparationBinding.toPIN2 (FirstComposition.toRetainedPublic pub)) hash pre.c1_root=ok (.Ok (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.transcript initial)) ∧
      AspisR1PublicPreparation.r1_wire.begin (retainedDigest D) pre initial=ok (.Ok challenges,after) ∧
      AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B)
        (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre after challenges none=ok (.Ok (retainedSem sem)) ∧
      AspisR1PublicPreparation.FinishModel.payload pre 2#u8=ok (.Ok payload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload=ok (.Ok root2) ∧
      root2.val=payload.val ∧ sem.roots=Array.make 2#usize [pre.c1_root,root2] := by
  have source := verify_return R B D pub bytes hash sem success
  obtain ⟨pre',initial',after',challenges',parsed',publicInit',begin',finish'⟩ :=
    AspisR1PublicPreparationPIN2.S1SemanticVerify.verify_success _ _ _ _ _ none _ source
  have parsed := AspisR1PublicPreparation.PIN2W7_PrefixGlue.parseAccepted_agree bytes pre' parsed'
  have begin := AspisR1PublicPreparation.PIN2W7_PrefixGlue.begin_agree (retainedDigest D) pre'
    (AspisR1PublicPreparation.PIN2W7_PrefixGlue.transcriptBack initial') challenges' after'
    (by rw [AspisR1PublicPreparation.PIN2W7_PrefixGlue.transcript_back]; exact begin')
  have finish : AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B)
      (retainedDigest D) (FirstComposition.toRetainedPublic pub)
      (AspisR1PublicPreparation.PIN2W7_PrefixGlue.prefixBack pre')
      (AspisR1PublicPreparation.PIN2W7_PrefixGlue.transcriptBack after')
      (AspisR1PublicPreparation.PIN2W7_PrefixGlue.challengesBack challenges') none=ok (.Ok (retainedSem sem)) := by
    unfold AspisR1PublicPreparation.PIN2W7_PrefixGlue.finish at finish'
    simp only [AspisR1PublicPreparation.PIN2W7_PrefixGlue.digest_round,
      AspisR1PublicPreparation.PIN2W7_PrefixGlue.fromPIN2_round] at finish'
    obtain ⟨r,hr,hk⟩ := bind_success _ _ _ finish'
    cases r with
    | Err e => cases hk
    | Ok v =>
      have hv : AspisR1PublicPreparation.PIN2W7_PrefixGlue.sem v=
          AspisR1PublicPreparation.PIN2W7_PrefixGlue.sem (retainedSem sem) :=
        core.result.Result.Ok.inj (Result.ok.inj hk)
      have := congrArg AspisR1PublicPreparation.PIN2W7_PrefixGlue.semBack hv
      simp only [AspisR1PublicPreparation.PIN2W7_PrefixGlue.sem_round] at this
      rw [hr,this]
  obtain ⟨payload,root2,hpayload,hcopy,hbytes,hroots⟩ :=
    AspisR1PublicPreparation.S1SemanticRootCopy.finish_roots R B (retainedDigest D)
      (FirstComposition.toRetainedPublic pub) _ _ _ (retainedSem sem) finish
  exact ⟨_,_,_,_,payload,root2,parsed,
    by rw [AspisR1PublicPreparation.PIN2W7_PrefixGlue.transcript_back]; exact publicInit',
    begin,finish,hpayload,hcopy,hbytes,hroots⟩

#print axioms verify_return
#print axioms verify_roots
end AspisR1CurrentCaller.S1SemanticInstallation
