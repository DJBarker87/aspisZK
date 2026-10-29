import NED_AfterEncodingCohort
import NED_LiveEncodingConstants
set_option autoImplicit false
noncomputable section
namespace NED_LiveEncodingCohort
open Aeneas Aeneas.Std Result NED_LateCarriers NED_LateValidatorCohorts NED_ErrorCarriers

def mapStateOuter {α E F State : Type} (f : E → F) :
    Result (core.result.Result α E × State) → Result (core.result.Result α F × State)
 | .ok (r,st) => .ok (mapResult f r,st)
 | .fail e => .fail e
 | .div => .div

theorem result (s : TSnapshot) (out : Slice U8) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 (toRawSnapshot s) out =
    mapStateOuter toRawPoolV1PairLiveSnapshotErrorV1
      (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out) := by
  rw [NBK_LiveResult.source]
  by_cases size : out.length = 800
  · rw [if_neg (not_not.mpr size)]
    have len : Slice.len out = 800#usize := by scalar_tac
    unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
    simp only [NED_LiveEncodingConstants.size,len,bne_self_eq_false,if_false]
    rw [NED_LateValidatorCohorts.snapshot]
    cases valid : NBH_LiveValidator.result s with
    | Err e => simp [mapResult,mapStateOuter,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame]
    | Ok u =>
      cases u
      simp only [mapResult,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,mapStateOuter]
      simp only [toRawSnapshot,AspisR1.JHf_Carrier.toPoolV1PairLiveSnapshotV1,
        AspisS6CurrentAdapterCarrier.fromPoolV1PairLiveSnapshotV1,
        NED_DigestCohorts.digest_encode,NED_EncoderLoopCohorts.live_loop,
        NED_LiveEncodingConstants.magic,NED_LiveEncodingConstants.version,NED_LiveEncodingConstants.format]
      have fill : core.slice.Slice.fill core.clone.CloneU8 out 0#u8 = ok NBK_LiveResult.zero := by
        rw [NBK_Fill.source]
        congr 1
        apply Subtype.ext
        change List.replicate out.length 0#u8 = List.replicate 800 0#u8
        rw [size]
      rw [fill]
      simp only [bind_tc_ok]
      have zero_size : NBK_LiveResult.zero.length = 800 := by
        simp only [NBK_LiveResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      have prepared_size : (NBK_LivePrepare.value s NBK_LiveResult.zero).length = 800 := by
        simp only [NBK_LivePrepare.value,Slice.length,NBK_LiveResult.zero,Array.to_slice,Array.repeat_val,
          List.length_setSlice!,List.length_set,List.length_replicate]
        rfl
      change NBK_LivePrepare.run s NBK_LiveResult.zero (fun iter bytes => do
        let encoded ← AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop iter bytes
        ok (core.result.Result.Ok (),encoded)) = _
      rw [NBK_LivePrepare.exact s NBK_LiveResult.zero zero_size]
      rw [NBK_LiveBytes.loop_exact s.frontier 0#usize (by decide) _ prepared_size]
      rfl
  · rw [if_pos size]
    have len : Slice.len out ≠ 800#usize := by scalar_tac
    simp only [AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1,
      NED_LiveEncodingConstants.size,ne_eq,bne_iff_ne,len,not_false_eq_true,if_true,mapStateOuter,mapResult,
      toRawPoolV1PairLiveSnapshotErrorV1]

#print axioms result
end NED_LiveEncodingCohort
