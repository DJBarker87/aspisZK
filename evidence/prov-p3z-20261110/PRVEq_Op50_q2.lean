import Aeneas
import NNH_HostCtx
import NOC_Run5bHost
import NNH_LaneModel
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_q1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le at' K Lane frontierLoop decodeLane)
open AspisR1

/-- the typed host record that op50 returns for a reference result (as in NNH_LaneModel.decode) -/
def laneOut (r : core.result.Result NCV_Reference.Lane Unit) :
    core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
      solana_program_error.ProgramError :=
  match r with
  | .Ok a => .Ok (NNH_LaneCarrier.native a)
  | .Err () => .Err .InvalidAccountData

/-- Deployed slot op50 = reference decode_lane_ref (carrier-mapped) = transcription, on every input
and every host context. -/
theorem op50_eq_transcription {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (b : Slice U8) :
    ∃ r, (NOC_HostCtx.sdk c).op50 b = ok (laneOut r) ∧
      NCV_Reference.decode_lane_ref b = ok r ∧ LCmp (decodeLane K0 (bytesOf b)) r := by
  obtain ⟨r, h, hc⟩ := decode_lane_ref_eq b
  refine ⟨r, ?_, h, hc⟩
  have hs : (NOC_HostCtx.sdk c).op50 = NNH_LaneModel.decode := rfl
  rw [hs]
  unfold NNH_LaneModel.decode
  rw [h]
  rfl

#print axioms op50_eq_transcription

end PCVY_Op50
