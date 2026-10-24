import S1WideViewFinalLengthV1
import S1QueryFixedProgramV1
import RawSamplerSuffixSourceFrames
import R1SelectedTranscriptParams
import R1QuerySamplerBridge
set_option autoImplicit false
noncomputable section
namespace AspisS1SelectedQueryPayload
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisR1PublicPreparation.PreparedHashCode.QueryPair
open AspisR1PublicPreparation.PreparedQueryMaterialize

/-- The literal model's message includes the EXACT source u32 length prefix.
No canonical encoding or independently chosen payload bytes are assumed. -/
def framedPayload (payload : Slice U8) : Bytes :=
  AspisR1.PublicInitFrame.lengthBytes (UScalar.cast .U32 (Slice.len payload)).val ++ rawBytes payload

theorem framedPayload_length (payload : Slice U8) :
    (framedPayload payload).length=4+payload.length := by
  simp only [framedPayload,List.length_append,AspisR1.PublicInitFrame.lengthBytes_length,
    rawBytes,List.length_map,Slice.length]

/-- The reached 2048-byte payload makes the source usize-to-u32 cast exact. -/
theorem source_length_cast (payload : Slice U8) (length : payload.length=2048) :
    (UScalar.cast .U32 (Slice.len payload)).val=2048 := by
  have size : (Slice.len payload).val=2048 := by
    simpa only [Slice.len,Usize.ofNatCore_val_eq] using length
  rw [UScalar.cast_val_eq,size]
  rfl

def selectedMessage (payload : Slice U8) (length : payload.length=2048) : AspisR1.SelectedTranscriptParams.Message :=
  ⟨framedPayload payload,by rw [framedPayload_length,length]; decide⟩

theorem selectedMessage_exact (payload : Slice U8) (length : payload.length=2048) :
    AspisR1.SelectedTranscriptParams.params.enc (selectedMessage payload length)=
      AspisR1.PublicInitFrame.lengthBytes 2048 ++ rawBytes payload := by
  change framedPayload payload=_
  rw [framedPayload,source_length_cast payload length]

def queryAbsorb (state : Array U8 32#usize) (payload : Slice U8) (length : payload.length=2048) :
    Addr AspisR1.SelectedTranscriptParams.L :=
  absorbA AspisR1.SelectedTranscriptParams.params (decodeState state)
    (AspisR1.SelectedTranscriptParams.params.lbl 31)
    (selectedMessage payload length).val (selectedMessage payload length).property

/-- Concrete selected address equality; size, source cast, model message and
label obligations are discharged, not supplied as an address-equality port. -/
theorem queryAbsorb_bytes (state : Array U8 32#usize) (payload : Slice U8) (length : payload.length=2048) :
    (queryAbsorb state payload length).toBytes=
      flatten (CallerStep.openingAbsorbParts state 191#u8 (UScalar.cast .U32 (Slice.len payload)) payload) := by
  rw [queryAbsorb,absorbA,Addr.toBytes_ofBytes,
    SamplerSuffixSourceFrames.opening_absorb_frame]
  rfl

/-- Full Program equality with the selected mathematical query constructor:
all seventeen reads, every reply branch, ordered queries and selected state.
This does not construct or assume an actual full-transcript Prefix. -/
theorem fixedQuery31_selected (state : Array U8 32#usize) (payload : Slice U8) (length : payload.length=2048) :
    fixedQuery31 state payload=
      rename Addr.toBytes
        (AspisR1.QuerySamplerBridge.sampler AspisR1.SelectedTranscriptParams.params
          (queryAbsorb state payload length) id).toProgram := by
  change Program.ask
      (flatten (CallerStep.openingAbsorbParts state 191#u8 (UScalar.cast .U32 (Slice.len payload)) payload))
      (fun absorbed => pairedBytesProgram
        (fun bs xs => R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed) 8 absorbed [] [])=
    Program.ask (queryAbsorb state payload length).toBytes (fun absorbed =>
      rename Addr.toBytes (AspisR1.QuerySampler.chain AspisR1.SelectedTranscriptParams.params
        (fun bs xs => R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed) 8 absorbed [] []).toProgram)
  rw [queryAbsorb_bytes]
  refine congrArg (Program.ask _) ?_
  funext absorbed
  with_reducible exact pairedBytesProgram_eq_model AspisR1.SelectedTranscriptParams.params _ _ _ _ _

#print axioms framedPayload_length
#print axioms source_length_cast
#print axioms selectedMessage_exact
#print axioms queryAbsorb_bytes
#print axioms fixedQuery31_selected
end AspisS1SelectedQueryPayload
