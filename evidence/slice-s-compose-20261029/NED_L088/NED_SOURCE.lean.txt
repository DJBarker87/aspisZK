import NED_LateCarriers
set_option autoImplicit false
noncomputable section
namespace NED_LateValidatorCohorts
open Aeneas Aeneas.Std Result NED_LateCarriers NED_ErrorCarriers
attribute [local instance] Classical.propDecidable

def mapResult {α E F : Type} (f : E → F) : core.result.Result α E → core.result.Result α F
  | .Ok x => .Ok x
  | .Err e => .Err (f e)

theorem after (s : TAfter) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate (toRawAfter s) =
    ok (mapResult toRawPoolV1PairVerifierTransportErrorV1 (NBH_Validators.afterResult s)) := by
  rw [NED_RawAfterValidator.afterstate]
  simp only [NED_RawAfterValidator.afterResult, NBH_Validators.afterResult, toRawAfter,
    AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1,
    AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1]
  repeat' split
  all_goals simp_all [mapResult,toRawPoolV1PairVerifierTransportErrorV1]

theorem snapshot (s : TSnapshot) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 (toRawSnapshot s) =
    ok (mapResult toRawPoolV1PairLiveSnapshotErrorV1 (NBH_LiveValidator.result s)) := by
  rw [NED_RawLiveValidator.source]
  simp only [NED_RawLiveValidator.result, NBH_LiveValidator.result, toRawSnapshot,
    AspisR1.JHf_Carrier.toPoolV1PairLiveSnapshotV1,
    AspisS6CurrentAdapterCarrier.fromPoolV1PairLiveSnapshotV1]
  repeat' split
  all_goals simp_all [mapResult,toRawPoolV1PairLiveSnapshotErrorV1]

#print axioms after
#print axioms snapshot
end NED_LateValidatorCohorts
