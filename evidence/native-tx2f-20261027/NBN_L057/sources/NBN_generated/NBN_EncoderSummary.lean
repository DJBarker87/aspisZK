import NBN_DigestResultDependency
set_option autoImplicit false
noncomputable section
namespace NBN_EncoderSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_terminal
abbrev Afterstate := NBH_Validators.Afterstate
abbrev Snapshot := NBH_LiveValidator.Snapshot
abbrev Encode := NBN_DigestResultDependency.Encode
abbrev NBN_Dep_DigestEncodeCanonical := NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical

def afterHeader (a : Afterstate) (output : Array U8 688#usize) (root : Array U8 32#usize) : Array U8 688#usize :=
  ⟨(((((((output.val.setSlice! 0 POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val).set
      4 POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION).set
      5 pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION).set
      6 pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION).set 7 1#u8).setSlice!
      8 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      16 root.val), by
        simp only [List.length_setSlice!,List.length_set,output.property]⟩

def liveHeader (a : Snapshot) (output : Slice U8) (root : Array U8 32#usize) : Slice U8 :=
  ⟨((((((((output.val.setSlice! 0 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val).set
      8 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION).setSlice!
      16 AspisR1.JFt_SnapshotConstants.formatArray.val).setSlice!
      48 a.pool.val).setSlice! 80 a.deployment_domain.val).setSlice!
      112 (core.num.U64.to_le_bytes a.sequence).val).setSlice!
      120 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      128 root.val), by
        simpa only [List.length_setSlice!,List.length_set] using output.property⟩


theorem after_header (a : Afterstate) (out : Array U8 688#usize) :
    afterHeader a out (DigestBytes.bytes a.next_root) = AfterstatePrepare.value a out := by rfl

theorem live_header (a : Snapshot) (out : Slice U8) :
    liveHeader a out (DigestBytes.bytes a.current_root) = NBK_LivePrepare.value a out := by rfl

/-- Source control summary; encoded child Results retain fail/div. -/
def after (encode : Encode) (a : Afterstate) :
    Result (core.result.Result (Array U8 688#usize) PoolV1PairVerifierTransportErrorV1) :=
  match NBH_Validators.afterResult a with
  | .Err e => ok (.Err e)
  | .Ok _ => do
    let root ← encode a.next_root
    let out ← NBN_DigestResultDependency.foldM encode
      (fun i b (o : Array U8 688#usize) => o.setSlice! (48+32*i) b.val)
      a.next_frontier.val 0 (afterHeader a (Array.repeat 688#usize 0#u8) root)
    ok (.Ok out)

def live (encode : Encode) (s : Snapshot) (out : Slice U8) :
    Result (core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 × Slice U8) :=
  if out.length ≠ 800 then ok (.Err .WrongLength,out)
  else match NBH_LiveValidator.result s with
    | .Err e => ok (.Err e,out)
    | .Ok _ => do
      let root ← encode s.current_root
      let written ← NBN_DigestResultDependency.foldM encode
        (fun i b (o : Slice U8) => o.setSlice! (160+32*i) b.val)
        s.frontier.val 0 (liveHeader s NBK_LiveResult.zero root)
      ok (.Ok (),written)

theorem after_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode) (a : Afterstate) :
    after encode a = encode_pool_v1_pair_verified_afterstate_v1 a := by
  rw [NBK_AfterstateResult.source]
  cases valid : NBH_Validators.afterResult a with
  | Err e => simp only [after,valid]
  | Ok u =>
    cases u
    simp only [after,valid]
    let prepared := AfterstatePrepare.value a (Array.repeat 688#usize 0#u8)
    have calls := NBN_DigestResultDependency.after_caller encode lower a valid prepared
    rw [calls.1]
    simp only [bind_tc_ok,after_header]
    rw [calls.2]
    rfl

theorem live_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : Snapshot) (out : Slice U8) :
    live encode s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out := by
  rw [NBK_LiveResult.source]
  by_cases size : out.length = 800
  · simp only [live,size,ne_eq,not_true_eq_false,if_false]
    cases valid : NBH_LiveValidator.result s with
    | Err e => rfl
    | Ok u =>
      cases u
      let prepared := NBK_LivePrepare.value s NBK_LiveResult.zero
      have calls := NBN_DigestResultDependency.live_caller encode lower s valid prepared
      rw [calls.1]
      simp only [bind_tc_ok,live_header]
      rw [calls.2]
      rfl
  · simp only [live,size,ne_eq,not_false_eq_true,if_true]

#print axioms after_header
#print axioms live_header
#print axioms after_source
#print axioms live_source
end NBN_EncoderSummary
