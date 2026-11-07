import NMT_345Decoder
import NFY_Part032
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
abbrev FormatError := NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
/-- Concrete CLOSED276; Rust errors and outer failures are not collapsed. -/
def validateCall (s : Statement) : Result (core.result.Result Unit FormatError) :=
 mapOuter (mapCore id NMT_345Dec.fromT13)
  (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
   (NMT_345Dec.toT8 s))
theorem validate_closed (s : Statement) : validateCall s =
 mapOuter (mapCore id NMT_345Dec.fromT13)
  (NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane
    NFY_NEM_LateOracle.late (NMT_345Dec.toT8 s)).1 := by
 have h := congrArg (fun x => x.1) (NFY_NEM_ValidatorComposed.result_state_effects (NMT_345Dec.toT8 s) ())
 dsimp only at h
 unfold validateCall
 rw [← h]
#print axioms validate_closed
end NMT_345
