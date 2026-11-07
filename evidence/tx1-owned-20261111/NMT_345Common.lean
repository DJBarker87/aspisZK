import NMT_345Decoder
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
abbrev Common := NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
def commonValue : Statement → Common
 | .PrivateTransfer c _ => c
 | .Withdrawal c _ => c
def commonCall (s : Statement) : Result Common := .ok (commonValue s)
/-- Complete immutable common projection through the same decoded owner. -/
theorem common_transport (s : Statement) :
 NMT_345Dec.toT7 (commonValue s) = NFY_NBN_StatementResult.common (NMT_345Dec.toT8 s) := by
 cases s <;> rfl
/-- CLOSED267, at that SAME transported statement, with no success premise. -/
theorem common_closed (s : Statement) :
 AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
  (NFY_NED_ReconstructCarriers.toRaw (NMT_345Dec.toT8 s)) =
 .ok (NFY_NED_ReconstructCarriers.toRawCommon (NMT_345Dec.toT7 (commonValue s))) := by
 rw [common_transport]
 exact NFY_NED_ReconstructCarriers.common_argument _
#print axioms common_transport
#print axioms common_closed
end NMT_345
