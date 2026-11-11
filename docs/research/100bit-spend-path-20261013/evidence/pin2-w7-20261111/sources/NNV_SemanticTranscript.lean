import NNH_Run5bCurrentShape
import LIB_VPublicTranscript
import PIN2W7_TranscriptCopy
/-! PIN2 W10 (2026-11-11): STATEMENT CHANGE (follows the approved definition change of
`LIB_VPublicTranscript.code` to the PIN2 public transcript).  `source`: right-hand side is the
copied-back PIN2 `public_transcript` on the copies,
`rmap (cres transcriptBack errorBack) (PIN2 r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D) (toPIN2 a.1) () key)`
(release: frozen `r1_semantic.public_transcript D a.1 () key`), proof via
`publicTranscriptPIN2_erasure` (release: `publicTranscript_erasure`).  `returned`: conclusion is the
PIN2-on-copies form `PIN2 public_transcript (digest copy) (toPIN2 a.1) () key = .ok (.Ok (PIN2W7_TranscriptCopy.transcript t))`
used by W7 everywhere (release: frozen `public_transcript D a.1 () key = .ok (.Ok t)`); same premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_SemanticTranscript
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem source (a : LIB_VCarriers.Public × RSL.B32) (env : RSL.Env) :
 (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 =
 PIN2W7_PrefixGlue.rmap (PIN2W7_PrefixGlue.cres PIN2W7_PrefixGlue.transcriptBack PIN2W7_PrefixGlue.errorBack)
  (AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest (LIB_VCode.digest env))
   (PreparationBinding.toPIN2 a.1) () (LIB_Env.nativeKey a.2)) := by
 rw [LIB_VPublicTranscript.source,PreparedHashCode.run_value,S1SemanticCode.publicTranscriptPIN2_erasure]

theorem returned (a : LIB_VCarriers.Public × RSL.B32) (env : RSL.Env)
 (t : LIB_VCarriers.Transcript)
 (called : LIB_VLib.publicTranscriptValue a env = .ok t) :
 AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest (LIB_VCode.digest env))
  (PreparationBinding.toPIN2 a.1) () (LIB_Env.nativeKey a.2) = .ok (.Ok (PIN2W7_TranscriptCopy.transcript t)) := by
 change LIB_VResult.value LIB_VRecords.host (.error .Public)
  (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 = .ok t at called
 rw [source] at called
 cases model : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest (LIB_VCode.digest env))
   (PreparationBinding.toPIN2 a.1) () (LIB_Env.nativeKey a.2) with
 | fail e => rw [model] at called; cases called
 | div => rw [model] at called; cases called
 | ok reply =>
  rw [model] at called
  cases reply with
  | Err e => cases called
  | Ok v =>
   change Except.ok (PIN2W7_PrefixGlue.transcriptBack v) = .ok t at called
   cases Except.ok.inj called
   rfl
#print axioms source
#print axioms returned
end AspisR1.NNV_SemanticTranscript
end
