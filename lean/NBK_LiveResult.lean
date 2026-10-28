import NBK_LivePrepare
import NBK_Fill
set_option autoImplicit false
noncomputable section
namespace NBK_LiveResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_tree_profile
abbrev Snapshot := PoolV1PairLiveSnapshotV1

def zero : Slice U8 := (Array.repeat 800#usize 0#u8).to_slice

def bytes (s : Snapshot) : Slice U8 :=
  NBK_LiveBytes.fold s.frontier.val 0 (NBK_LivePrepare.value s zero)

theorem success (s : Snapshot) (output : Slice U8)
    (size : output.length = 800)
    (valid : validate_pool_v1_pair_live_snapshot_v1 s = ok (.Ok ())) :
    encode_pool_v1_pair_live_snapshot_v1 s output = ok (.Ok (),bytes s) := by
  have len : Slice.len output = 800#usize := by scalar_tac
  simp only [encode_pool_v1_pair_live_snapshot_v1,len,
    POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, bne_self_eq_false, if_false,
    valid,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  have fill : core.slice.Slice.fill core.clone.CloneU8 output 0#u8 = ok zero := by
    rw [NBK_Fill.source]
    congr 1
    apply Subtype.ext
    change List.replicate output.length 0#u8 = List.replicate 800 0#u8
    rw [size]
  rw [fill]
  simp only [bind_tc_ok]
  change NBK_LivePrepare.run s zero (fun iter out => do
    let encoded ← encode_pool_v1_pair_live_snapshot_v1_loop iter out
    ok (core.result.Result.Ok (),encoded)) = _
  rw [NBK_LivePrepare.exact s zero (by simp only [zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]; rfl)]
  have prepared_size : (NBK_LivePrepare.value s zero).length = 800 := by
    simp only [NBK_LivePrepare.value,Slice.length,zero,Array.to_slice,Array.repeat_val,List.length_setSlice!,List.length_set,List.length_replicate]
    rfl
  rw [NBK_LiveBytes.loop_exact s.frontier 0#usize (by decide) _ prepared_size]
  rfl

theorem source (s : Snapshot) (output : Slice U8) :
    encode_pool_v1_pair_live_snapshot_v1 s output =
      if output.length ≠ 800 then ok (.Err .WrongLength,output)
      else match NBH_LiveValidator.result s with
        | .Ok _ => ok (.Ok (),bytes s)
        | .Err e => ok (.Err e,output) := by
  by_cases size : output.length = 800
  · rw [if_neg (not_not.mpr size)]
    have val := NBH_LiveValidator.source s
    cases r : NBH_LiveValidator.result s with
    | Ok u =>
      cases u
      rw [r] at val
      exact success s output size val
    | Err e =>
      rw [r] at val
      have len : Slice.len output = 800#usize := by scalar_tac
      simp only [encode_pool_v1_pair_live_snapshot_v1,len,
        POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, bne_self_eq_false, if_false,
        val,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      rfl
  · rw [if_pos size]
    have len : Slice.len output ≠ 800#usize := by scalar_tac
    simp only [encode_pool_v1_pair_live_snapshot_v1,
      POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, ne_eq, bne_iff_ne, len, not_false_eq_true, if_true]

#print axioms success
#print axioms source
end NBK_LiveResult
