import S6NativeSnapshotStoreV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeSnapshotLoopStep
open AspisR1TerminalDecoder
abbrev Digest := Array aspis_core.field.M31 8#usize
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Digest)
abbrev next := core.iter.adapters.enumerate.IteratorEnumerate.next
  (core.iter.traits.iterator.IteratorSliceIter Digest)
abbrev body := pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body

theorem body_done (iter iter' : Iter) (output : Slice U8)
    (done : next iter = ok (none,iter')) :
    body iter output = ok (ControlFlow.done output) := by
  simp only [body, pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body,
    done, bind_tc_ok]
  rfl

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n = ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h), Result.ofOption]
  rfl

theorem body_write (iter iter' : Iter) (output : Slice U8)
    (level : Usize) (node : Digest) (bytes : Array U8 32#usize)
    (reached : next iter = ok (some (level,node),iter'))
    (range : level.val < 20) (size : output.length=800)
    (encoded : atomic_statement.encode_digest_canonical node = ok bytes) :
    body iter output = ok (ControlFlow.cont (iter',AspisS6NativeSnapshotStore.write output (160+32*level.val) bytes)) := by
  have mul : 32#usize * level = ok (Usize.ofNatCore (32*level.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (32*level.val) = _
    exact mk _ _
  have add : 160#usize + Usize.ofNatCore (32*level.val) (by scalar_tac) =
      ok (Usize.ofNatCore (160+32*level.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (160+32*level.val) = _
    exact mk _ _
  have stop : Usize.ofNatCore (160+32*level.val) (by scalar_tac) + 32#usize =
      ok (Usize.ofNatCore (192+32*level.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (160+32*level.val+32) = _
    have eqn : 160+32*level.val+32 = 192+32*level.val := by omega
    simp only [eqn]
    exact mk _ _
  simp only [body, pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body,
    reached, bind_tc_ok]
  change (do
    let i ← 32#usize * level
    let start ← 160#usize + i
    let stop ← start + 32#usize
    let (s, back) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start, «end» := stop}
    let a ← atomic_statement.encode_digest_canonical node
    let src ← lift (Array.to_slice a)
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
    ok (ControlFlow.cont (iter',back copied))) = _
  simp only [mul, add, stop, encoded, bind_tc_ok]
  have run := AspisS6NativeSnapshotStore.store_exact output
    (Usize.ofNatCore (160+32*level.val) (by scalar_tac))
    (Usize.ofNatCore (192+32*level.val) (by scalar_tac)) bytes
    (by change 160+32*level.val ≤ 192+32*level.val; omega)
    (by change 192+32*level.val ≤ output.length; omega)
    (by change 192+32*level.val-(160+32*level.val)=32; omega)
  unfold AspisS6NativeSnapshotStore.store at run
  change (do
    let (s, back) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8)
      output {start := Usize.ofNatCore (160+32*level.val) _, «end» := Usize.ofNatCore (192+32*level.val) _}
    let src ← lift (Array.to_slice bytes)
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
    ok (ControlFlow.cont (iter',back copied))) = _
  have lifted := congrArg (fun r => do
    let a ← r
    ok (ControlFlow.cont (iter',a) : ControlFlow (Iter × Slice U8) (Slice U8))) run
  cases indexed : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) output
      {start := Usize.ofNatCore (160+32*level.val) (by scalar_tac),
       «end» := Usize.ofNatCore (192+32*level.val) (by scalar_tac)} with
  | fail e => simp only [indexed, bind_tc_fail] at run; cases run
  | div => simp only [indexed, bind_tc_div] at run; cases run
  | ok pair =>
    rcases pair with ⟨s,back⟩
    simp only [indexed, bind_tc_ok] at lifted ⊢
    change (do
      let a ← (do
        let src ← lift (Array.to_slice bytes)
        let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
        ok (back copied))
      ok (ControlFlow.cont (iter',a))) = _ at lifted
    have proj : (Usize.ofNatCore (160+32*level.val) (by scalar_tac)).val = 160+32*level.val := by rfl
    simpa only [bind_assoc_eq, bind_tc_ok, proj] using lifted

#print axioms mk
#print axioms body_done
#print axioms body_write
end AspisS6NativeSnapshotLoopStep
