import S1SelectedQueryMapV1
import R1LiteralByteSampler
set_option autoImplicit false
noncomputable section
namespace AspisS1SelectedQueryPayload
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation.PreparedQueryMaterialize

/-- The selected source frame at the actual model Prefix state, with its
message bytes constructed from the source payload. No freely chosen bytes. -/
theorem queryAbsorb_prefix (P : AspisR1.LiteralTranscript.Prefix) (payload : Slice U8)
    (length : payload.length=2048) :
    queryAbsorb (encodeState (AspisR1.UnifiedSampler.stateOf AspisR1.SelectedTranscriptParams.params
      (AspisR1.LiteralTranscript.erasePrefix P))) payload length=
      AspisR1.UnifiedSampler.absorb AspisR1.SelectedTranscriptParams.params 31
        (AspisR1.LiteralTranscript.erasePrefix P) (selectedMessage payload length) := by
  unfold queryAbsorb AspisR1.UnifiedSampler.absorb
  rw [state_roundtrip]
  rfl

/-- EXACT complete byte-program equality for selected literal row31, on ANY
actual Prefix carrier. It does not assert that a source caller's preceding
transcript has already been proved equal to that Prefix; that join stays open. -/
theorem literal_query_program (P : AspisR1.LiteralTranscript.Prefix) (payload : Slice U8)
    (length : payload.length=2048) :
    AspisV8R19.OracleProgramOps.bind
      (fixedQuery31 (encodeState (AspisR1.UnifiedSampler.stateOf AspisR1.SelectedTranscriptParams.params
        (AspisR1.LiteralTranscript.erasePrefix P))) payload)
      (fun result => .done (AspisR1.UnifiedSampler.liftQuery result))=
      (AspisR1.LiteralByteSampler.samp 31 P (.payload (selectedMessage payload length))).toProgram := by
  rw [fixedQuery31_selected_map _ _ payload length,queryAbsorb_prefix]
  unfold AspisR1.LiteralByteSampler.samp AspisR1.ProgramSamplerMap.map
  rw [AspisR1.ProgramSamplerMap.toProgram_fromProgram]
  unfold AspisR1.LiteralTranscript.samp
  simp only [AspisR1.LiteralTranscript.erase]
  rw [AspisR1.UnifiedSampler.row_query]

#print axioms queryAbsorb_prefix
#print axioms literal_query_program
end AspisS1SelectedQueryPayload
