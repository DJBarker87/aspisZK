import S2K_Iterator

/-! Totality of the actual eight-word digest encoder by a decreasing iterator
invariant. No canonicality assumption is needed for byte serialization. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S2K.DigestTotal
open AspisR1TerminalDecoder
abbrev Word := aspis_core.field.M31
abbrev Digest := Array Word 8#usize
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Word)
def cursor (rows : Digest) (count : Usize) : Iter := ⟨⟨rows.to_slice,count.val⟩,count⟩
abbrev next := core.iter.adapters.enumerate.IteratorEnumerate.next
  (core.iter.traits.iterator.IteratorSliceIter Word)
abbrev body := atomic_statement.encode_digest_canonical_loop.body

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n = ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h), Result.ofOption]
  rfl

theorem next_row (rows : Digest) (count : Usize) (range : count.val < 8) :
    next (cursor rows count) = ok
      (some (count,rows.val[count.val]'(by have := rows.property; change rows.val.length = 8 at this; omega)),
       cursor rows (Usize.ofNatCore (count.val+1) (by scalar_tac))) := by
  have inc : count + 1#usize = ok (Usize.ofNatCore (count.val+1) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (count.val+1) = _
    exact mk _ _
  have valid : count.val < rows.to_slice.len.val := by
    simp only [Array.to_slice, Slice.len_val, rows.property]
    exact range
  simp only [next, cursor, core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next, dif_pos valid, bind_tc_ok, inc]
  rfl

theorem body_word (rows : Digest) (count : Usize) (range : count.val < 8)
    (output : Array U8 32#usize) :
    body (cursor rows count) output = ok (cont
      (cursor rows (Usize.ofNatCore (count.val+1) (by scalar_tac)),
       output.setSlice! (4*count.val)
         (core.num.U32.to_le_bytes (rows.val[count.val]'(by have := rows.property; change rows.val.length = 8 at this; omega))).val)) := by
  have mul : count * 4#usize = ok (Usize.ofNatCore (4*count.val) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (count.val*4) = _
    have hn : count.val*4 = 4*count.val := by omega
    simp only [hn]
    exact mk _ _
  have stop : Usize.ofNatCore (4*count.val) (by scalar_tac) + 4#usize =
      ok (Usize.ofNatCore (4*count.val+4) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (4*count.val+4) = _
    exact mk _ _
  simp only [body, atomic_statement.encode_digest_canonical_loop.body, next_row rows count range, bind_tc_ok]
  change (do
    let i ← count * 4#usize
    let stop ← i + 4#usize
    let (s, back) ← core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) output {start := i, «end» := stop}
    let a ← aspis_core.field.M31.to_le_bytes (rows.val[count.val]'_)
    let src ← lift a.to_slice
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
    ok (cont (_,back copied))) = _
  simp only [mul, stop, bind_tc_ok, aspis_core.field.M31.to_le_bytes]
  have place : 4*count.val ≤ 28 := by omega
  have room : 4 ≤ 32-4*count.val := by omega
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Array.to_slice]
  simp [Slice.length, Slice.len, output.property, core.slice.Slice.copy_from_slice,
    List.slice, Array.from_slice, lift, place, Nat.min_eq_left room]
  rfl

theorem exhausted (rows : Digest) :
    next (cursor rows 8#usize) = ok (none,cursor rows 8#usize) := by
  have invalid : ¬ (8#usize).val < rows.to_slice.len.val := by
    simp only [Array.to_slice, Slice.len_val, rows.property]
    decide
  simp only [next, cursor, core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next, dif_neg invalid, bind_tc_ok]

def Inv (rows : Digest) (s : Iter × Array U8 32#usize) : Prop :=
  ∃ k : Usize, k.val ≤ 8 ∧ s.1 = cursor rows k

theorem loop_total (rows : Digest) (count : Usize) (bound : count.val ≤ 8)
    (output : Array U8 32#usize) :
    WP.spec (atomic_statement.encode_digest_canonical_loop (cursor rows count) output)
      (fun _ => True) := by
  unfold atomic_statement.encode_digest_canonical_loop
  refine loop.spec_decr_nat
    (fun s : Iter × Array U8 32#usize => 8-s.1.count.val)
    (Inv rows) (fun _ : Array U8 32#usize => True)
    (fun s : Iter × Array U8 32#usize => body s.1 s.2)
    (cursor rows count,output) ?_ ⟨count,bound,rfl⟩
  rintro ⟨iter,out⟩ ⟨k,hk,same⟩
  change iter = cursor rows k at same
  simp only [same]
  by_cases more : k.val < 8
  · rw [body_word rows k more out]
    change (Inv rows (_,_) ∧ (8-(Usize.ofNatCore (k.val+1) _).val) < 8-k.val)
    refine ⟨⟨Usize.ofNatCore (k.val+1) (by scalar_tac),?_,rfl⟩,?_⟩
    · change k.val+1 ≤ 8; omega
    · change 8-(k.val+1) < 8-k.val; omega
  · have eqk : k = 8#usize := by scalar_tac
    subst k
    have stopped : body (cursor rows 8#usize) out = ok (done out) := by
      simp only [body, atomic_statement.encode_digest_canonical_loop.body,
        exhausted rows, bind_tc_ok]
      rfl
    rw [stopped]
    trivial

theorem total (rows : Digest) :
    ∃ bytes, atomic_statement.encode_digest_canonical rows = ok bytes := by
  have h := loop_total rows 0#usize (by decide) (Array.repeat 32#usize 0#u8)
  have run : atomic_statement.encode_digest_canonical rows =
      atomic_statement.encode_digest_canonical_loop (cursor rows 0#usize) (Array.repeat 32#usize 0#u8) := by
    rfl
  rw [← run] at h
  cases result : atomic_statement.encode_digest_canonical rows with
  | fail e => simp only [result,WP.spec,WP.theta] at h
  | div => simp only [result,WP.spec,WP.theta] at h
  | ok bytes => exact ⟨bytes,rfl⟩

#print axioms mk
#print axioms next_row
#print axioms body_word
#print axioms exhausted
#print axioms loop_total
#print axioms total
end AspisR1.S2K.DigestTotal
