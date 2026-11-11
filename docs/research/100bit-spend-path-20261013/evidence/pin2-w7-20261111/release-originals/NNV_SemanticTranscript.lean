import NNH_Run5bCurrentShape
import LIB_VPublicTranscript
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_SemanticTranscript
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem source (a : LIB_VCarriers.Public × RSL.B32) (env : RSL.Env) :
 (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 =
 r1_semantic.public_transcript (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2) := by
 rw [LIB_VPublicTranscript.source,PreparedHashCode.run_value,S1SemanticCode.publicTranscript_erasure]

theorem returned (a : LIB_VCarriers.Public × RSL.B32) (env : RSL.Env)
 (t : LIB_VCarriers.Transcript)
 (called : LIB_VLib.publicTranscriptValue a env = .ok t) :
 r1_semantic.public_transcript (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2) = .ok (.Ok t) := by
 change LIB_VResult.value LIB_VRecords.host (.error .Public)
  (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 = .ok t at called
 rw [source] at called
 cases model : r1_semantic.public_transcript (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2) with
 | fail e => rw [model] at called; cases called
 | div => rw [model] at called; cases called
 | ok reply =>
  rw [model] at called
  cases reply with
  | Err e => cases called
  | Ok v =>
   change Except.ok v = .ok t at called
   cases Except.ok.inj called
   rfl
#print axioms source
#print axioms returned
end AspisR1.NNV_SemanticTranscript
end
