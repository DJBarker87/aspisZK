import AspisR197CurrentBytes.FunsBytes

set_option autoImplicit false

namespace AspisV8R19.R200CurrentBytesRank

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR156FullFreeze

abbrev CurrentIter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter AspisR156FullFreeze.aspis_core.field.QM31)

def rank (st : CurrentIter × alloc.vec.Vec Std.U8) : Nat :=
  st.1.iter.slice.val.length - st.1.iter.i

theorem body_continuation_rank (iter : CurrentIter) (b : alloc.vec.Vec Std.U8)
    (iter1 : CurrentIter) (b1 : alloc.vec.Vec Std.U8)
    (h : AspisR197CurrentBytes.bytes_loop.body iter b =
      .ok (.cont (iter1, b1))) :
    rank (iter1, b1) < rank (iter, b) := by
  unfold rank
  have hactive : iter.iter.i < iter.iter.slice.val.length := by
    by_contra hstop
    simp [AspisR197CurrentBytes.bytes_loop.body,
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.iter.traits.iterator.IteratorSliceIter,
      core.slice.iter.IteratorSliceIter.next, Slice.len, hstop] at h
  simp [AspisR197CurrentBytes.bytes_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.iter.traits.iterator.IteratorSliceIter,
    core.slice.iter.IteratorSliceIter.next, Slice.len, hactive, lift] at h ⊢
  cases hc : (iter.count + 1#usize : Result Usize) with
  | fail e => simp [hc] at h
  | div => simp [hc] at h
  | ok count =>
      simp only [hc, bind_tc_ok] at h
      cases hx : alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice U8) b
          { start := iter.count.wrapping_mul 16#usize,
            «end» := (iter.count.wrapping_mul 16#usize).wrapping_add 16#usize } with
      | fail e => simp [hx] at h
      | div => simp [hx] at h
      | ok pair =>
          rcases pair with ⟨out, back⟩
          simp only [hx, bind_tc_ok] at h
          cases hw : AspisR156FullFreeze.aspis_core.field.QM31.write_le_bytes
              (iter.iter.slice[iter.iter.i]) out with
          | fail e =>
              erw [hw] at h
              cases h
          | div =>
              erw [hw] at h
              cases h
          | ok written =>
              erw [hw] at h
              have hpair := ControlFlow.cont.inj (Result.ok.inj h)
              have hi := congrArg
                (fun st : CurrentIter × alloc.vec.Vec U8 => st.1.iter.i) hpair
              have hs := congrArg
                (fun st : CurrentIter × alloc.vec.Vec U8 => st.1.iter.slice.val.length) hpair
              change iter.iter.i + 1 = iter1.iter.i at hi
              change iter.iter.slice.val.length = iter1.iter.slice.val.length at hs
              omega

#print axioms body_continuation_rank

end AspisV8R19.R200CurrentBytesRank
