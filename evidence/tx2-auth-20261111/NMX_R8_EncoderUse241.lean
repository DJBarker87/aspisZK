import NMX_R7_Encoder241
import NMX_R8_MapBind
set_option autoImplicit false
noncomputable section
namespace NMX_R8_EncoderUse241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError

theorem full (s : LIBB_PoolCarriers.Statement)
 (next : NMX_R7_Encoder241.Bytes1880 → RSL.Spec Reply) (later : RSL.Bytes → RSL.RS Unit)
 (rest : ∀ b, Simulates (NMS_R2N_RSLError.reply id) (next b)
  (later (NMS_R2N_RSLScalars.bytes b.to_slice))) :
 Simulates (NMS_R2N_RSLError.reply id)
  (NMS_R2N_RawTry.literal (NMX_R7_Encoder241.mapped s) next)
  (RSL.RS.bind (RSL.RS.lift (LIBB_PoolLib.library.encodeStatement s)) fun encoded =>
   RSL.RS.bind (RSL.RS.ofOption encoded .invalidInstructionData) later) := by
 change Simulates _
  (NMS_R2N_RawTry.literal
   (RSL.Spec.map NMX_R7_Encoder241.reply (liftResult (LIBB_PoolEncode.code s))) next)
  (RSL.RS.bind (RSL.RS.lift (RSL.Spec.map LIBB_PoolEncode.option (liftResult (LIBB_PoolEncode.code s)))) _)
 rw [NMS_R2N_RawTry.normalize]
 unfold NMS_R2N_RawTry.simple
 rw [NMX_R8_MapBind.map_bind,NMX_R8_MapBind.lift_bind,NMX_R8_MapBind.map_bind]
 apply NMS_R2N_Interpreted.bind id (NMS_R2N_RSLError.reply id)
 · intro env o run
   simpa only [NMS_R2N_ObservationMaps.identity] using run
 · intro r
   cases r with
   | Err e =>
     change Simulates _ (RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidInstructionData : Reply))
      (RSL.RS.bind (RSL.RS.throw .invalidInstructionData) later)
     rw [RSL.RS.bind_throw]
     exact NMS_R2N_Interpreted.pure _ _
   | Ok b =>
     change Simulates _ (next b) (RSL.RS.bind (RSL.RS.pure _) later)
     rw [RSL.RS.bind_pure]
     exact rest b
#print axioms full
end NMX_R8_EncoderUse241
end
