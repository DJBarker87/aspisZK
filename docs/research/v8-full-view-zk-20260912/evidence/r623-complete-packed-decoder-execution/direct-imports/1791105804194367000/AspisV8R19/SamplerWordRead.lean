import AspisR72Sampler.Funs
import Mathlib.Tactic

/-! Safe four-byte reads used by the actual generated inner sampler.
The backend and sampler success distribution are not assumed. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerWordRead
open Aeneas Aeneas.Std Result AspisR72Sampler

def small (n : Nat) (hn : n ≤ 32) : Usize :=
  UScalar.ofNatCore n (by have := Usize.cMax_bound; scalar_tac)

theorem small_val (n : Nat) (hn : n ≤ 32) : (small n hn).val = n := rfl

theorem try_small (n : Nat) (hn : n ≤ 32) :
    UScalar.tryMk .Usize n = .ok (small n hn) := by
  have hb : UScalar.inBounds .Usize n := by
    have := Usize.cMax_bound; scalar_tac
  have hs := UScalar.tryMk_eq .Usize n
  cases h : UScalar.tryMk .Usize n with
  | fail e => simp only [h] at hs; exact False.elim (hs hb)
  | div => simp only [h] at hs
  | ok a =>
      simp only [h] at hs
      congr 1
      apply UScalar.eq_of_val_eq
      exact hs.1

def four (b : Array U8 32#usize) (i : Nat) (hi : i ≤ 28) : Array U8 4#usize :=
  ⟨(b.val.drop i).take 4,by
    have hb : b.val.length=32 := b.property
    simp only [List.length_take,List.length_drop,hb]
    change min 4 (32-i)=4
    omega⟩

theorem slice_success (b : Array U8 32#usize) (i : Usize) (hi : i.val ≤ 28) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U8)) b
      {start:=i, «end»:=small (i.val+4) (by omega)} =
      .ok (Array.to_slice (four b i.val hi)) := by
  have hb : b.val.length=32 := b.property
  simp [core.array.Array.index,core.ops.index.IndexSlice,core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    Array.to_slice,Slice.length,small_val,four,List.slice,hb]
  omega

theorem conversion_success (a : Array U8 4#usize) :
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
      (Array.to_slice a) = .ok (.Ok a) := by
  simp [core.array.TryFromArrayCopySlice.try_from,Array.to_slice,Slice.length,a.property]

theorem unwrap_success (a : Array U8 4#usize) :
    core.result.Result.unwrap core.fmt.DebugTryFromSliceError (.Ok a) = .ok a := rfl

def read (b : Array U8 32#usize) (j : Usize) : Result (U32 × Usize) := do
  let i ← j * 4#usize
  let finish ← i + 4#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) b {start:=i, «end»:=finish}
  let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let word ← lift (core.num.U32.from_le_bytes a)
  let next ← j + 1#usize
  ok (word,next)

theorem read_success (b : Array U8 32#usize) (j : Usize) (hj : j.val < 8) :
    read b j = .ok (core.num.U32.from_le_bytes (four b (j.val*4) (by omega)),
      small (j.val+1) (by omega)) := by
  have hm : (j * 4#usize : Result Usize) = .ok (small (j.val*4) (by omega)) := by
    change UScalar.tryMk .Usize (j.val*4) = _
    exact try_small _ _
  have ha : (small (j.val*4) (by omega) + 4#usize : Result Usize) =
      .ok (small (j.val*4+4) (by omega)) := by
    change UScalar.tryMk .Usize (j.val*4+4) = _
    exact try_small _ _
  have hn : (j + 1#usize : Result Usize) = .ok (small (j.val+1) (by omega)) := by
    change UScalar.tryMk .Usize (j.val+1) = _
    exact try_small _ _
  have hs := slice_success b (small (j.val*4) (by omega))
    (by simpa only [small_val] using (show j.val*4 ≤ 28 by omega))
  simp only [small_val] at hs
  simp only [read,hm,ha,bind_tc_ok,hs,conversion_success,unwrap_success,lift,hn]

theorem mask_bound (word : U32) : (word &&& field.P).val ≤ 2147483647 := by
  change (word.bv &&& field.P.bv).toNat ≤ _
  rw [BitVec.toNat_and]
  simpa [field.P] using (Nat.and_le_right (n:=word.bv.toNat) (m:=field.P.bv.toNat))

theorem accepted_canonical (word : U32) (h : word &&& field.P ≠ field.P) :
    (word &&& field.P).val < 2147483647 := by
  have hb := mask_bound word
  have hn : (word &&& field.P).val ≠ 2147483647 := by
    intro he
    apply h
    apply UScalar.eq_of_val_eq
    simpa [field.P] using he
  omega

#print axioms small_val
#print axioms try_small
#print axioms slice_success
#print axioms conversion_success
#print axioms unwrap_success
#print axioms read_success
#print axioms mask_bound
#print axioms accepted_canonical
end AspisV8R19.SamplerWordRead
