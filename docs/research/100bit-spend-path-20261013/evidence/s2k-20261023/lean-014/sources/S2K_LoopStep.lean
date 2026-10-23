import S2K_SourcePorts

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.LoopStep
open AspisR1TerminalDecoder
abbrev Digest := Array aspis_core.field.M31 8#usize
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Digest)
abbrev next := core.iter.adapters.enumerate.IteratorEnumerate.next
  (core.iter.traits.iterator.IteratorSliceIter Digest)
abbrev body := pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body

theorem body_done (iter iter' : Iter) (output : Array U8 688#usize)
    (done : next iter = ok (none,iter')) :
    body iter output = ok (ControlFlow.done output) := by
  simp only [body, pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body,
    done, bind_tc_ok]
  rfl

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n = ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h), Result.ofOption]

theorem body_write (iter iter' : Iter) (output : Array U8 688#usize)
    (level : Usize) (node : Digest) (bytes : Array U8 32#usize)
    (reached : next iter = ok (some (level,node),iter'))
    (range : level.val < 20)
    (encoded : atomic_statement.encode_digest_canonical node = ok bytes) :
    body iter output = ok (ControlFlow.cont (iter',output.setSlice! (48+32*level.val) bytes.val)) := by
  have mul : 32#usize * level = ok (Usize.ofNatCore (32*level.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (32*level.val) = _
    exact mk _ _
  have add : 48#usize + Usize.ofNatCore (32*level.val) (by scalar_tac) =
      ok (Usize.ofNatCore (48+32*level.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (48+32*level.val) = _
    exact mk _ _
  have stop : Usize.ofNatCore (48+32*level.val) (by scalar_tac) + 32#usize =
      ok (Usize.ofNatCore (80+32*level.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (48+32*level.val+32) = _
    have eqn : 48+32*level.val+32 = 80+32*level.val := by omega
    simp only [eqn]
    exact mk _ _
  simp only [body, pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body,
    reached, bind_tc_ok]
  change (do
    let i ← 32#usize * level
    let start ← 48#usize + i
    let stop ← start + 32#usize
    let (s, back) ← core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) output {start, «end» := stop}
    let a ← atomic_statement.encode_digest_canonical node
    let src ← lift (Array.to_slice a)
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
    ok (ControlFlow.cont (iter',back copied))) = _
  simp only [mul, add, stop, encoded, bind_tc_ok]
  have run := SourceStore.store_exact output
    (Usize.ofNatCore (48+32*level.val) (by scalar_tac))
    (Usize.ofNatCore (80+32*level.val) (by scalar_tac)) bytes
    (by change 48+32*level.val ≤ 80+32*level.val; omega)
    (by change 80+32*level.val ≤ 688; omega)
    (by change 80+32*level.val-(48+32*level.val)=32; omega)
  unfold SourceStore.store at run
  change (do
    let (s, back) ← core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      output {start := Usize.ofNatCore (48+32*level.val) _, «end» := Usize.ofNatCore (80+32*level.val) _}
    let src ← lift (Array.to_slice bytes)
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
    ok (ControlFlow.cont (iter',back copied))) = _
  exact congrArg (fun r => r.map (fun a => ControlFlow.cont (iter',a))) run

#print axioms mk
#print axioms body_done
#print axioms body_write
end AspisR1.S2K.LoopStep
