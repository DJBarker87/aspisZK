import NNH_EncodeOk
import LIBB_PoolEmit
set_option autoImplicit false
noncomputable section
namespace NNH_EmitModel
open Aeneas Aeneas.Std AdapterRw NND_Carrier
/-- Returned-value projection of the SAME canonical emit source computation.
Its source runtime still receives and records the original return-data bytes. -/
def code (s : LIBB_PoolCarriers.Statement) :
 Result (core.result.Result Unit solana_program_error.ProgramError) := do
 let out ← LIBB_PoolEmit.code s
 Result.ok (match out with
  | .Ok _ => .Ok ()
  | .Err e => .Err (unerror (NMS_R2N_RSLError.error e)))

theorem ok (s : LIBB_PoolCarriers.Statement)
 (success : LIBB_PoolEmit.evaluator s=.ok ()) : code s=.ok (.Ok ()) := by
 unfold LIBB_PoolEmit.evaluator LIBB_PoolEmit.observation at success
 cases source : LIBB_PoolEmit.code s with
 | fail e => rw [source] at success; cases success
 | div => rw [source] at success; cases success
 | ok reply => cases reply with
   | Err e => rw [source] at success; cases success
   | Ok state => unfold code; rw [source]; rfl
#print axioms ok
end NNH_EmitModel
