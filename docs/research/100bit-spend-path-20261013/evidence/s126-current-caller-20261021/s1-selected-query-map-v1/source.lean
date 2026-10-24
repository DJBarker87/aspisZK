import S1SelectedQueryPayloadV1
import S1QueryPairedBindV1
set_option autoImplicit false
noncomputable section
namespace AspisS1SelectedQueryPayload
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode.QueryPair
open AspisR1PublicPreparation.PreparedQueryMaterialize

/-- Pure challenge wrapping preserves the entire selected seventeen-ask
program. Used below for the actual literal transcript challenge constructor. -/
theorem fixedQuery31_selected_map {C : Type} (G : Except Nat (List Nat) × State → C)
    (state : Array U8 32#usize) (payload : Slice U8) (length : payload.length=2048) :
    AspisV8R19.OracleProgramOps.bind (fixedQuery31 state payload) (fun out => .done (G out))=
      rename Addr.toBytes (AspisR1.QuerySamplerBridge.sampler AspisR1.SelectedTranscriptParams.params
        (queryAbsorb state payload length) G).toProgram := by
  change Program.ask
      (flatten (CallerStep.openingAbsorbParts state 191#u8 (UScalar.cast .U32 (Slice.len payload)) payload))
      (fun absorbed => AspisV8R19.OracleProgramOps.bind
        (pairedBytesProgram (fun bs xs => R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed) 8 absorbed [] [])
        (fun out => .done (G out)))=
    Program.ask (queryAbsorb state payload length).toBytes (fun absorbed =>
      rename Addr.toBytes (AspisR1.QuerySampler.chain AspisR1.SelectedTranscriptParams.params
        (fun bs xs => G (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 bs xs absorbed)) 8 absorbed [] []).toProgram)
  rw [queryAbsorb_bytes]
  refine congrArg (Program.ask _) ?_
  funext absorbed
  rw [paired_bind_done]
  with_reducible exact pairedBytesProgram_eq_model AspisR1.SelectedTranscriptParams.params _ _ _ _ _

#print axioms fixedQuery31_selected_map
end AspisS1SelectedQueryPayload
