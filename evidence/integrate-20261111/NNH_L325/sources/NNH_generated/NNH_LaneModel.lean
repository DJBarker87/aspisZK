import NNH_LaneCarrier
import NNH_MAccountCarrier
import NND_LaneReturned
set_option autoImplicit false
namespace NNH_LaneModel
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier
/-- The reviewed217 reference at its original slice, re-encoded into the
actual SDK nominal lane type. Native row credit remains with the ledger. -/
def decode (b : Slice U8) : Result (core.result.Result
 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
 solana_program_error.ProgramError) := do
 let r ← NCV_Reference.decode_lane_ref b
 Result.ok (match r with
  | .Ok a => .Ok (NNH_LaneCarrier.native a)
  | .Err () => .Err .InvalidAccountData)

def install (base : Ops) : Ops := {base with op50 := decode}

theorem bytes (b : Slice U8) :
 NND_Carrier.bytes b=b.val.map NMX_R3_ByteCarrier.byte := by
 unfold NND_Carrier.bytes
 exact List.map_congr_left (fun x _ => NNH_LaneCarrier.byte x)

/-- All input lengths, full error/Ok carrier map. No concrete frontier
recurrence is evaluated and no decoder-success clause is assumed. -/
theorem mapped (b : Slice U8) :
 outer (reply NND_Carrier.lane) (decode b)=
 .ok (NND_LaneReturned.value (NND_Carrier.bytes b)) := by
 obtain ⟨r,call,same⟩ := NMX_R3_LaneTotal.value b
 have target : NND_LaneReturned.value (NND_Carrier.bytes b)=
  NND_Returned.option (NMX_R3_LaneCarrier.result r) .invalidAccountData := by
  unfold NND_LaneReturned.value
  rw [bytes,←same]
 rw [target]
 unfold decode
 rw [call]
 cases r with
 | Err u => cases u; rfl
 | Ok a =>
  change Result.ok (Except.ok (NND_Carrier.lane (NNH_LaneCarrier.native a))) = _
  rw [NNH_LaneCarrier.lane]
  rfl

theorem returned (b : Slice U8) (env : RSL.Env)
 (o : RSL.Obs (Except RSL.ProgramError RSL.LaneState)) (r : Except RSL.ProgramError RSL.LaneState)
 (law : RSL.TX2_217.Ref (NND_Carrier.bytes b) env o) (returned : o.exit=.ret r) :
 outer (reply NND_Carrier.lane) (decode b)=.ok r :=
 (mapped b).trans (congrArg Result.ok (NND_LaneReturned.returned _ env o r law returned).symm)

#print axioms bytes
#print axioms mapped
#print axioms returned
end NNH_LaneModel
