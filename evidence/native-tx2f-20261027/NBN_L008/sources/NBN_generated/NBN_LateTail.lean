import NBN_LatePrepare
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBN_LateTail
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_tree_profile
abbrev Statement := PoolV1PairLatePublicStatementV1
abbrev Error := PoolV1PairLatePublicStatementErrorV1

def run (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) := do
  let i7 ← 32#usize + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (s15, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r, s16) ← encode_pool_v1_pair_live_snapshot_v1 s.live_snapshot s15
  match r with
  | .Err e => ok (.Err (.LiveSnapshot e), back s16)
  | .Ok _ =>
    let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s.candidate_afterstate
    match r2 with
    | .Err e => ok (.Err (.Afterstate e), back s16)
    | .Ok bytes =>
      let (dest, back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back s16) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (), back2 copied)

def status (s : Statement) : core.result.Result Unit Error :=
  match NBH_LiveValidator.result s.live_snapshot with
  | .Err e => .Err (.LiveSnapshot e)
  | .Ok _ => match NBH_Validators.afterResult s.candidate_afterstate with
    | .Err e => .Err (.Afterstate e)
    | .Ok _ => .Ok ()

def value (s : Statement) (output : Slice U8) : Slice U8 :=
  match NBH_LiveValidator.result s.live_snapshot with
  | .Err _ => output
  | .Ok _ =>
    let live := output.setSlice! 32 (NBK_LiveResult.bytes s.live_snapshot).val
    match NBH_Validators.afterResult s.candidate_afterstate with
    | .Err _ => live
    | .Ok _ => live.setSlice! 832 (AfterstateEncoding.bytes s.candidate_afterstate).val

 theorem live_length (s : NBK_LiveResult.Snapshot) :
    (NBK_LiveResult.bytes s).length = 800 := by
  have fold_length (xs : List (Array U32 8#usize)) (i : Nat) (out : Slice U8) :
      (NBK_LiveBytes.fold xs i out).length = out.length := by
    induction xs generalizing i out with
    | nil => rfl
    | cons x xs ih =>
      simpa only [NBK_LiveBytes.fold, ih, Slice.length, Slice.setSlice!,List.length_setSlice!]
  simp only [NBK_LiveResult.bytes,fold_length,NBK_LivePrepare.value,
    Slice.length,NBK_LiveResult.zero,Array.to_slice,Array.repeat_val,
    List.length_setSlice!,List.length_set,List.length_replicate]
  rfl

 theorem exact (s : Statement) (output : Slice U8) (size : output.length = 1520) :
    run s output = ok (status s, value s output) := by
  have len : output.val.length = 1520 := size
  unfold run
  simp only [POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]
  have add : 32#usize + 800#usize = ok 832#usize := by
    have h : (32#usize + 800#usize) ⦃ r => r = 832#usize ⦄ := by step*
    obtain ⟨r, call, same⟩ := WP.spec_imp_exists h
    exact same ▸ call
  rw [add]
  simp only [bind_tc_ok, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
  simp only [Slice.length,Slice.len,len]
  simp only [show (32:Nat) ≤ 832 by decide, show (832:Nat) ≤ 1520 by decide, ↓reduceDIte,bind_tc_ok]
  rw [NBK_LiveResult.source]
  simp only [Slice.length,Slice.slice,List.length_take,List.length_drop,len]
  simp only [show ¬ (min (1520-32) (832-32) ≠ 800) by decide,if_false]
  cases hv : NBH_LiveValidator.result s.live_snapshot with
  | Err e => simp [hv,status,value,bind_tc_ok]
  | Ok u =>
    cases u
    simp only [hv,bind_tc_ok]
    rw [NBK_AfterstateResult.source]
    cases ha : NBH_Validators.afterResult s.candidate_afterstate with
    | Err e => simp [ha,status,value,hv,bind_tc_ok]
    | Ok u =>
      cases u
      simp [ha,hv,status,value,bind_tc_ok,
        core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice,Array.to_slice,Slice.length,Slice.len,
        Slice.slice,List.slice,List.length_setSlice!,len,live_length,
        (AfterstateEncoding.bytes s.candidate_afterstate).property,Slice.setSlice!,lift]

#print axioms live_length
#print axioms exact
end NBN_LateTail
