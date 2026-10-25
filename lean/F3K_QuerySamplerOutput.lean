import F3K_ConcreteDecode
import F3K_QueryDecoderSource
import F3J_QueryAbsorber
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QuerySamplerOutput
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open FS2.Duplex R0C.V3

theorem output {Hash : Type} (D : aspis_core.Digest32 Hash)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (out : Array U32 22#usize)
    (success : QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries
      Query31ConcreteDriverTraceFacts.sourceDefaultState embed) D before 31#u8 payload=ok (.Ok out,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (a : Addr SelectedTranscriptParams.L)
    (address : a.toBytes=flatten (CallerStep.openingAbsorbParts before.state 191#u8
      (UScalar.cast .U32 (Slice.len payload)) payload)) :
    (eval (fun a => H a.toBytes)
      (QuerySamplerBridge.sampler SelectedTranscriptParams.params a id).toProgram).2=
      (.ok (out.val.map (fun x=>x.val)),decodeState after.state) := by
  obtain ⟨absorbed,blocks,advances,selected,absorbedCall,values,decode,carried⟩ :=
    F3K_QueryDecoderSource.source _ D before after 31#u8 payload out success
  obtain ⟨tag,digestState,add,digest,absEq⟩ := PAln_OpeningCalls.absorb_success
    D before absorbed 31#u8 payload absorbedCall
  change ok (191#u8)=ok tag at add
  cases Result.ok.inj add
  have ds : absorbed.state=digestState := congrArg (fun t=>t.state) absEq
  have oracle : H a.toBytes=decodeState absorbed.state := by
    rw [address,ds]
    exact (backend _ ⟨before.hash,_,digestState,rfl,digest⟩).symm
  have lists := F3K_QueryValues.deterministic values H backend
  have model := F3K_ConcreteDecode.accepted blocks advances out selected (decodeState absorbed.state) decode
  unfold QuerySamplerBridge.sampler
  change (eval (fun a=>H a.toBytes) (QuerySampler.chain SelectedTranscriptParams.params
    (fun bs xs=>id (Q22.scanOut 8 Q22.q0 bs xs (H a.toBytes))) 8 (H a.toBytes) [] []).toProgram).2=_
  rw [oracle,QuerySampler.chain_out]
  simp only [List.nil_append,id_eq]
  rw [← lists.1,← lists.2]
  rw [carried]
  exact model

#print axioms output
end AspisR1.F3K_QuerySamplerOutput
end
