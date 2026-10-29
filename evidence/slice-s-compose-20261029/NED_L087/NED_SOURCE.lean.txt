import NED_RawCarrierInverses
import NED_RawAfterValidator
import NED_RawLiveValidator
import NBH_LiveValidator
set_option autoImplicit false
noncomputable section
namespace NED_LateCarriers
open Aeneas Aeneas.Std Result
abbrev TSnapshot := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev TAfter := AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev TLate := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev RSnapshot := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev RAfter := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev RLate := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def toRawSnapshot (s : TSnapshot) : RSnapshot := AspisR1.JHf_Carrier.toPoolV1PairLiveSnapshotV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairLiveSnapshotV1 s)
def fromRawSnapshot (s : RSnapshot) : TSnapshot := AspisS6CurrentAdapterCarrier.toPoolV1PairLiveSnapshotV1
  (AspisR1.JHf_Carrier.fromPoolV1PairLiveSnapshotV1 s)
def toRawAfter (s : TAfter) : RAfter := AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 s)
def fromRawAfter (s : RAfter) : TAfter := AspisS6CurrentAdapterCarrier.toPoolV1PairVerifiedAfterstateV1
  (AspisR1.JHf_Carrier.fromPoolV1PairVerifiedAfterstateV1 s)
def toRawLate (s : TLate) : RLate := AspisR1.JHf_Carrier.toPoolV1PairLatePublicStatementV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairLatePublicStatementV1 s)
def fromRawLate (s : RLate) : TLate := AspisS6CurrentAdapterCarrier.toPoolV1PairLatePublicStatementV1
  (AspisR1.JHf_Carrier.fromPoolV1PairLatePublicStatementV1 s)

theorem snapshot_to_from (s : RSnapshot) : toRawSnapshot (fromRawSnapshot s) = s := by cases s <;> rfl
theorem snapshot_from_to (s : TSnapshot) : fromRawSnapshot (toRawSnapshot s) = s := by cases s <;> rfl
theorem after_to_from (s : RAfter) : toRawAfter (fromRawAfter s) = s := by cases s <;> rfl
theorem after_from_to (s : TAfter) : fromRawAfter (toRawAfter s) = s := by cases s <;> rfl
theorem late_to_from (s : RLate) : toRawLate (fromRawLate s) = s := by cases s <;> rfl
theorem late_from_to (s : TLate) : fromRawLate (toRawLate s) = s := by cases s <;> rfl

#print axioms snapshot_to_from
#print axioms snapshot_from_to
#print axioms after_to_from
#print axioms after_from_to
#print axioms late_to_from
#print axioms late_from_to
end NED_LateCarriers
