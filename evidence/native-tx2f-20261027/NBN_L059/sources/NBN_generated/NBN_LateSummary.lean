import NBN_EncoderSummary
import NBN_LateResult
set_option autoImplicit false
noncomputable section
namespace NBN_LateSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
abbrev Statement := PoolV1PairLatePublicStatementV1
abbrev Error := PoolV1PairLatePublicStatementErrorV1
abbrev Encode := NBN_EncoderSummary.Encode
abbrev NBN_Dep_DigestEncodeCanonical := NBN_EncoderSummary.NBN_Dep_DigestEncodeCanonical

def tail (encode : NBN_EncoderSummary.Encode) (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) := do
  let i7 ← 32#usize + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (s15, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r, s16) ← NBN_EncoderSummary.live encode s.live_snapshot s15
  match r with
  | .Err e => ok (.Err (.Snapshot e), back s16)
  | .Ok _ =>
    let r2 ← NBN_EncoderSummary.after encode s.candidate_afterstate
    match r2 with
    | .Err e => ok (.Err (.Afterstate e), back s16)
    | .Ok bytes =>
      let (dest, back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back s16) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (), back2 copied)


theorem tail_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : Statement) (output : Slice U8) : tail encode s output = NBN_LateTail.run s output := by
  unfold tail NBN_LateTail.run
  simp only [NBN_EncoderSummary.live_source encode lower,NBN_EncoderSummary.after_source encode lower]

def run (encode : Encode) (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) :=
  if output.length ≠ 1520 then ok (.Err .WrongLength,output)
  else if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index then ok (.Err .AfterstateIndexMismatch,output)
  else do
    let filled ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
    NBN_LatePrepare.run filled (tail encode s)

theorem source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : Statement) (output : Slice U8) :
    run encode s output = encode_pool_v1_pair_late_public_statement_v1 s output := by
  unfold run
  by_cases size : output.length = 1520
  · rw [if_neg (not_not.mpr size)]
    by_cases index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
        some s.candidate_afterstate.next_pair_index
    · rw [if_neg (not_not.mpr index)]
      have same : tail encode s = NBN_LateTail.run s := funext (tail_source encode lower s)
      rw [same]
      exact (NBN_LateResult.factor s output size index).symm
    · rw [if_pos index]
      exact (NBK_LatePreflight.wrong_index s output size index).symm
  · rw [if_pos size]
    exact (NBK_LatePreflight.wrong_length s output size).symm

#print axioms tail_source
#print axioms source
end NBN_LateSummary
