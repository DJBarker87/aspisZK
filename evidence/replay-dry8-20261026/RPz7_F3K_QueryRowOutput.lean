import RPz7_F3K_QuerySamplerOutput
import RPz7_F3K_QueryAddress
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryRowOutput
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open FS2.Duplex

theorem output {Hash : Type} (D : aspis_core.Digest32 Hash)
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
    (eval H (LiteralByteSampler.samp 31 P m).toProgram).2=
      (TranscriptView.Value.queries (.ok (out.val.map (fun x=>x.val))),decodeState after.state) := by
  let a := UnifiedSampler.absorb SelectedTranscriptParams.params 31 (LiteralTranscript.erasePrefix P) b
  have address := F3K_QueryAddress.address before.state payload fits P b state frame
  have raw := F3K_QuerySamplerOutput.output D embed before after payload out success H backend a address
  rw [QuerySamplerBridge.output] at raw
  rw [LiteralByteSampler.eval_eq]
  change (eval (fun a=>H a.toBytes) (UnifiedSampler.samp SelectedTranscriptParams.params _ 31
    (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram).2=_
  rw [erased,UnifiedSampler.row_query,QuerySamplerBridge.output]
  exact congrArg UnifiedSampler.liftQuery raw

#print axioms output
end AspisR1.F3K_QueryRowOutput
end
