import RPz7_F3K_QueryCode
import RPz7_F3K_QueryRowOutput
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryFull
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem exact_row {Hash : Type} (D : aspis_core.Digest32 Hash)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (out : Array U32 22#usize)
    (success : QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries
      Query31ConcreteDriverTraceFacts.sourceDefaultState embed) D before 31#u8 payload=ok (.Ok out,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (fits : payload.val.length<4294967296)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (frame : b.val=OraclePortCompactDraft.framed (MultiproofConeCanonical.bytesOf payload.val)) :
    eval H (LiteralByteSampler.samp 31 P m).toProgram=
      (observe (run (PreparedQueryEffects.queries effects
        (Query31ConcreteMaterializedSchedule.concreteBoundaries
          Query31ConcreteDriverTraceFacts.sourceDefaultState embed) D before 31#u8 payload)).1,
       (TranscriptView.Value.queries (.ok (out.val.map (fun x=>x.val))),decodeState after.state)) := by
  obtain ⟨absorbed,calls,ha,pairs,code⟩ := F3K_QueryCode.observed _ D before after payload out success
  have log := F3J_QueryAbsorber.ordered D before absorbed payload ha H backend calls pairs fits P m b erased state frame
  exact Prod.ext (log.trans code.symm)
    (F3K_QueryRowOutput.output D embed before after payload out success H backend fits P m b erased state frame)

#print axioms exact_row
end AspisR1.F3K_QueryFull
end
