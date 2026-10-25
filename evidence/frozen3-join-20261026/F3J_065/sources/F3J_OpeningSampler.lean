import F3J_OpeningFacts
import F3J_OpeningFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_OpeningSampler
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses

theorem payload {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : transcript.Transcript Hash} {row : U8} {payload : Slice U8}
    {block : Array U8 32#usize} (c : F3J_OpeningFacts.Calls D before after row payload block)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (positive : row.val≠0) (notReseed : row.val≠26) (notQuery : row.val≠31) (below : row.val<33)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (framing : b.val=PublicInitFrame.lengthBytes (UScalar.cast .U32 (Slice.len payload)).val++rawBytes payload) :
    eval H (LiteralByteSampler.samp row.val P m).toProgram=
      (F3J_OpeningFacts.log c,
       (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ row.val (decodeState block)),decodeState after.state)) := by
  let params := SelectedTranscriptParams.params
  have added := UScalar.add_equiv 160#u8 row
  rw [c.tag_add] at added
  have tagValue : c.tag.val=160+row.val := by simpa using added.2.1
  have tag : params.lbl row.val=decodeByte c.tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label row.val).val=c.tag.val
    rw [SelectedTranscriptParams.label_val row.val (by omega),tagValue]
  have address : (UnifiedSampler.absorb params row.val (LiteralTranscript.erasePrefix P) b).toBytes=
      flatten (CallerStep.openingAbsorbParts before.state c.tag (UScalar.cast .U32 (Slice.len payload)) payload) := by
    unfold UnifiedSampler.absorb
    rw [state,tag,absorbA,Addr.toBytes_ofBytes,F3J_OpeningFrame.absorb]
    change AspisV8R19.DuplexFrames.absorb (bytes (decodeState before.state)) (decodeByte c.tag) b.val=_
    rw [framing]
    rfl
  have consistent := F3J_OpeningFacts.consistent c H backend
  have ha := consistent _ (List.mem_cons_self)
  have hb := consistent _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hs := consistent _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  change decodeState c.absorbed=H (flatten _) at ha
  change decodeState block=H (flatten _) at hb
  change decodeState c.state=H (flatten _) at hs
  rw [squeeze_address params] at hb
  rw [advance_address params] at hs
  rw [LiteralByteSampler.eval_eq]
  change mapView Addr.toBytes (eval (fun a => H a.toBytes)
    (UnifiedSampler.samp params _ row.val (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram)=_
  rw [erased,UnifiedSampler.row_ordinary params _ row.val positive notReseed notQuery,DuplexSamplers.plain_eval]
  simp only [mapView,List.map_cons,List.map_nil]
  rw [address,← ha,← hb,← hs]
  unfold F3J_OpeningFacts.log
  have afterState : after.state=c.state := congrArg (fun t => t.state) c.carried
  rw [squeeze_address params,advance_address params,afterState]
  rfl

#print axioms payload
end AspisR1.F3J_OpeningSampler
end
