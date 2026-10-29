import NED_ErrorCarriers
import NED_CodecComposition
import JHf_Carrier14
import S6CurrentAdapterCarrierV1
set_option autoImplicit false
noncomputable section
namespace NED_ReconstructCarriers
open Aeneas Aeneas.Std Result
abbrev Terminal := NBN_StatementResult.Statement
abbrev Raw := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev RawCommon := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def toRaw (s : Terminal) : Raw := AspisR1.JHf_Carrier.toPoolV1PairForestTerminalStatementV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 s)
def fromRaw (s : Raw) : Terminal := AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1
  (AspisR1.JHf_Carrier.fromPoolV1PairForestTerminalStatementV1 s)
def toRawCommon (c : Common) : RawCommon := AspisR1.JHf_Carrier.toPoolV1PairForestTerminalCommonV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalCommonV1 c)
def fromRawCommon (c : RawCommon) : Common := AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalCommonV1
  (AspisR1.JHf_Carrier.fromPoolV1PairForestTerminalCommonV1 c)

theorem common_roundtrip (c : Common) : fromRawCommon (toRawCommon c) = c := by
  unfold fromRawCommon toRawCommon
  rw [AspisR1.JHf_Carrier.from_toPoolV1PairForestTerminalCommonV1]
  exact AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalCommonV1 c

theorem statement_roundtrip (s : Terminal) : fromRaw (toRaw s) = s := by
  unfold fromRaw toRaw
  rw [AspisR1.JHf_Carrier.from_toPoolV1PairForestTerminalStatementV1]
  exact AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1 s

theorem common_argument (s : Terminal) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common (toRaw s) =
    ok (toRawCommon (NBN_StatementResult.common s)) := by
  cases s <;> rfl

theorem parts_argument (s : Terminal) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.statement_public_common (toRaw s) =
    ok (NBN_StatementResult.parts s) := by
  cases s <;> rfl

#print axioms common_roundtrip
#print axioms statement_roundtrip
#print axioms common_argument
#print axioms parts_argument
end NED_ReconstructCarriers
