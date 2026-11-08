import NMX_R7_VerifierSource241
import LIBB_PoolEmit
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Emit241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def raw : Except RSL.ProgramError Unit → core.result.Result Unit solana_program_error.ProgramError
 | .ok () => .Ok ()
 | .error e => .Err (NMS_R2N_RSLError.raw e)

def meaning (s : LIBB_PoolCarriers.Statement) :=
 RSL.Spec.map raw (LIBB_PoolLib.library.emitResult s)

theorem reply (r : Except RSL.ProgramError Unit) : NMS_R2N_RSLError.reply id (raw r) = r := by
 cases r with
 | ok unit => cases unit; rfl
 | error e => exact congrArg Except.error (NMS_R2N_RSLError.right e)

theorem full (s : LIBB_PoolCarriers.Statement) :
 Simulates (NMS_R2N_RSLError.reply id) (meaning s) (LIBB_PoolLib.library.emitResult s) :=
 NMS_R2N_ObservationMaps.cancel raw _ reply _

theorem live (s : LIBB_PoolCarriers.Statement) : NMX_R6_Nonempty.Live (meaning s) := by
 apply NMX_R6_Nonempty.mapped
 intro env
 exact ⟨_,rfl⟩
#print axioms reply
#print axioms full
#print axioms live
end NMX_R8_Emit241
end
