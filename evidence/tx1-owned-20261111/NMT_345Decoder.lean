import NMT_345Dec_T13
import NMT_345Carriers
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
abbrev Statement := NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
/-- Concrete CLOSED332, complete Result with its full decoded statement. -/
def decodeCall (bytes : Slice U8) : Result (core.result.Result Statement PE) :=
 mapOuter (mapCore (fun s => NMT_345Dec.fromT8
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 s)) fromPE)
  (AspisS6CurrentCodecInstallation.decode bytes)
theorem decode_closed (bytes : Slice U8) : decodeCall bytes =
 mapOuter (mapCore (fun s => NMT_345Dec.fromT8
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 s)) fromPE)
  (NFY_NEX_PublicModel.run bytes) := by
 have h := congrArg (fun x => x.1) (NFY_NEX_PublicModel.result_state_effects bytes ())
 dsimp only at h
 unfold decodeCall
 rw [← h]
#print axioms decode_closed
end NMT_345
