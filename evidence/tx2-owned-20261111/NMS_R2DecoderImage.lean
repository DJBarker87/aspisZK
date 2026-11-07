import NMS_R2RequestTotal
import NMS_R2ByteImage
set_option autoImplicit false
noncomputable section
namespace NMS_R2DecoderImage
open Aeneas Aeneas.Std Result AdapterRw
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
/-- Exact native request result classification. Outer fail/div cannot occur,
as established on every symbolic byte input by NMS_R2RequestTotal.total. -/
def option (data : Slice U8) : Option Request :=
 match AspisR1.NFY_JHd_RequestNative.decode data with
 | .ok (.Ok q) => some q
 | _ => none

def decode (data : RSL.Bytes) : Option Request :=
 if bound : data.length ≤ Usize.max then option (NMS_R2ByteImage.native data bound) else none

def reply (decoded : Option Request) : core.result.Result Request solana_program_error.ProgramError :=
 match decoded with | some q => .Ok q | none => .Err .InvalidInstructionData

/-- The source decoder followed by the actual frozen map_err closure. -/
def value (data : Slice U8) : Result (core.result.Result Request solana_program_error.ProgramError) := do
 let decoded ← AspisR1.NFY_JHd_RequestNative.decode data
 core.result.Result.map_err
  r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  decoded ()

theorem source (data : Slice U8) : value data = ok (reply (option data)) := by
 obtain ⟨decoded,run⟩ := NMS_R2RequestTotal.total data
 unfold value option
 rw [run,bind_tc_ok]
 cases decoded <;> rfl

theorem same_input (data : Slice U8) : decode (NMS_R2N_RSLScalars.bytes data) = option data := by
 have bound : (NMS_R2N_RSLScalars.bytes data).length ≤ Usize.max := by
   rw [NMS_R2N_RSLScalars.bytes_length]
   exact data.property
 unfold decode
 rw [dif_pos bound,NMS_R2ByteImage.left]

/-- Full native observation law for the canonical Option decoder slot,
including every rejecting input. No successful decoder premise is retained. -/
theorem full (data : Slice U8) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply id)
  (NMS_R2N_Interpreted.liftResult (value data))
  (RSL.RS.ofOption (decode (NMS_R2N_RSLScalars.bytes data)) .invalidInstructionData) := by
 rw [source,same_input]
 cases decoded : option data <;> exact NMS_R2N_Interpreted.pure _ _
#print axioms source
#print axioms same_input
#print axioms full
end NMS_R2DecoderImage
