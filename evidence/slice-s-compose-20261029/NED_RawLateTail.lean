import NED_LiveEncodingCohort
import NBN_LateTail
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NED_RawLateTail
open Aeneas Aeneas.Std Result AspisR1.S2K
open AspisR1AdapterReconstruct.aspis_statement
open pool_v1.pair_tree_profile
abbrev Statement := NED_LateCarriers.TLate
abbrev Error := PoolV1PairLatePublicStatementErrorV1

def run (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) := do
  let i7 ← 32#usize + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (s15, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r, s16) ← encode_pool_v1_pair_live_snapshot_v1 (NED_LateCarriers.toRawSnapshot s.live_snapshot) s15
  match r with
  | .Err e => ok (.Err (.Snapshot e), back s16)
  | .Ok _ =>
    let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (NED_LateCarriers.toRawAfter s.candidate_afterstate)
    match r2 with
    | .Err e => ok (.Err (.Afterstate e), back s16)
    | .Ok bytes =>
      let (dest, back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back s16) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (), back2 copied)

 theorem exact (s : Statement) (output : Slice U8) (size : output.length = 1520) :
    run s output = ok (NED_LateValidatorCohorts.mapResult NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1
      (NBN_LateTail.status s), NBN_LateTail.value s output) := by
  have len : output.val.length = 1520 := size
  unfold run
  simp only [NED_LiveEncodingConstants.size]
  have add : 32#usize + 800#usize = ok 832#usize := by
    have h : (32#usize + 800#usize) ⦃ r => r = 832#usize ⦄ := by step*
    obtain ⟨r, call, same⟩ := WP.spec_imp_exists h
    exact same ▸ call
  rw [add]
  simp only [bind_tc_ok]
  simp [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Slice.length,Slice.len,len]
  rw [NED_LiveEncodingCohort.result,NBK_LiveResult.source]
  simp [Slice.length, Slice.slice,List.slice,len]
  cases hv : NBH_LiveValidator.result s.live_snapshot with
  | Err e =>
    simp [NED_LiveEncodingCohort.mapStateOuter,NED_AfterEncodingCohort.mapOuter,NED_LateValidatorCohorts.mapResult,NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1,hv,NBN_LateTail.status,NBN_LateTail.value,bind_tc_ok]
    apply Subtype.ext
    simp only [List.setSlice!,List.length_take,List.length_drop,len]
    simp only [show min 800 (1520-32) = 800 by decide,
      show min 800 (min 800 (1520-32)) = 800 by decide]
    simp only [List.take_take,Nat.min_self]
    have restored := List.take_append_drop 800 (output.val.drop 32)
    simp only [List.drop_drop] at restored
    simpa only [List.append_assoc, restored, List.take_append_drop]
  | Ok u =>
    cases u
    simp only [hv,bind_tc_ok,NED_LiveEncodingCohort.mapStateOuter,NED_LateValidatorCohorts.mapResult]
    rw [NED_AfterEncodingCohort.result,NBK_AfterstateResult.source]
    cases ha : NBH_Validators.afterResult s.candidate_afterstate with
    | Err e => simp [NED_LiveEncodingCohort.mapStateOuter,NED_AfterEncodingCohort.mapOuter,NED_LateValidatorCohorts.mapResult,NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1,ha,NBN_LateTail.status,NBN_LateTail.value,hv,bind_tc_ok,Slice.setSlice!]
    | Ok u =>
      cases u
      simp [NED_LiveEncodingCohort.mapStateOuter,NED_AfterEncodingCohort.mapOuter,NED_LateValidatorCohorts.mapResult,NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1,ha,hv,NBN_LateTail.status,NBN_LateTail.value,bind_tc_ok,
        core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice,Array.to_slice,Slice.length,Slice.len,
        Slice.slice,List.slice,List.length_setSlice!,len,NBN_LateTail.live_length,
        (AfterstateEncoding.bytes s.candidate_afterstate).property,Slice.setSlice!,lift]

#print axioms exact
end NED_RawLateTail
