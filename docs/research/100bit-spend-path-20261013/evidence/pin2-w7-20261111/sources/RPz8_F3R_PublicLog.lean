import RPz7_F3J_InitialLog
import RPz7_F3K_CodeStep
import RPz7_S1SemanticCodePublicTranscriptExactV1
import PIN2_S1SemanticCodeVerifyExactV1
/-! PIN2 W9 (2026-11-11): STATEMENT CHANGE.  `PublicInitCall.serialized` is the PIN2
serializer (W7), so `log` is now stated for the call the PIN2 verifier makes,
`S1SemanticCode.publicTranscriptPIN2` (release: the frozen `publicTranscript`); the log value
`[initPair init]` is unchanged.  The proof is the release script on the PIN2 lift plus the
copy-back step; the PIN2 domain bytes are the frozen ones (`PIN2W7_TranscriptCopy.domain_eq`).
New: `publicPIN2_success`, the PIN2 `public_transcript` on the copies from a successful
`publicTranscriptPIN2` (inverse of the copy-back). -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_PublicLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceGlobalOracleInitial
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- A pure continuation adds nothing to the log. -/
theorem bind_pure_log {A B : Type} (p : Code A) (f : A → B) :
    (run (PreparedHashCode.bind p (fun x => pure (f x)))).1=(run p).1 := by
  rw [AuS1_Trace.run_bind]
  generalize run p = q
  rcases q with ⟨l,r⟩
  cases r with
  | ok a => exact List.append_nil l
  | fail e => rfl
  | div => rfl

/-- The release `log` script on the PIN2 lift (on the copies). -/
theorem logLift {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : Array U8 32#usize} {before : r1_wire.SemanticTranscript Hash}
    (init : PublicInitCall D pub root before) :
    observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript (PIN2W7_TranscriptCopy.digest D)
      (PreparationBinding.toPIN2 pub) before.hash root)).1=[initPair init] := by
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript
  rw [init.serialized]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript
  try simp only
  rw [init.converted]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  try simp only
  simp only [lift]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,
    F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  rw [PIN2W7_TranscriptCopy.domain_eq]
  erw [F3K_CodeStep.digest_success _ _ _ _ init.digest]
  rfl

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : Array U8 32#usize} {before : r1_wire.SemanticTranscript Hash}
    (init : PublicInitCall D pub root before) :
    observe (run (S1SemanticCode.publicTranscriptPIN2 D pub before.hash root)).1=[initPair init] := by
  unfold S1SemanticCode.publicTranscriptPIN2
  erw [bind_pure_log]
  exact logLift init

/-- A successful `publicTranscriptPIN2` is a successful PIN2 `public_transcript` on the copies. -/
theorem publicPIN2_success {Hash : Type} (D : aspis_core.Digest32 Hash)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : Hash)
    (root : Array U8 32#usize) (t : r1_wire.SemanticTranscript Hash)
    (h : erase (S1SemanticCode.publicTranscriptPIN2 D pub hash root)=ok (.Ok t)) :
    AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
      (PreparationBinding.toPIN2 pub) hash root=ok (.Ok (PIN2W7_TranscriptCopy.transcript t)) := by
  rw [S1SemanticCode.publicTranscriptPIN2_erasure] at h
  revert h
  cases AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
    (PreparationBinding.toPIN2 pub) hash root with
  | ok v =>
    cases v with
    | Ok t' =>
      intro h
      simp only [PIN2W7_PrefixGlue.rmap,PIN2W7_PrefixGlue.cres] at h
      have same : PIN2W7_PrefixGlue.transcriptBack t'=t := core.result.Result.Ok.inj (Result.ok.inj h)
      rw [← same,PIN2W7_PrefixGlue.transcript_back]
    | Err e =>
      intro h
      simp only [PIN2W7_PrefixGlue.rmap,PIN2W7_PrefixGlue.cres] at h
      cases h
  | fail e => intro h; cases h
  | div => intro h; cases h

#print axioms bind_pure_log
#print axioms logLift
#print axioms log
#print axioms publicPIN2_success
end AspisR1.F3R_PublicLog
end
