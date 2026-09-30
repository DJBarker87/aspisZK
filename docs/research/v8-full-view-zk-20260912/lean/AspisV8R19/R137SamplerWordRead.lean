import AspisR137Transcript.Funs
import AspisV8R19.SamplerWordRead

/-! Bounded wrapping-index bridge for the exact R137 sampler extraction.
The source uses wrapping `usize` arithmetic, whereas the older checked sampler
leaf uses `Result`-valued arithmetic.  On the source cursor invariant both
forms are equal.  No oracle or distribution claim is made here. -/
set_option autoImplicit false
namespace AspisV8R19.R137SamplerWordRead

open Aeneas Aeneas.Std Result
open AspisV8R19.SamplerWordRead

theorem wrapping_mul_checked (w : Usize) (hw : w.val ≤ 8) :
    lift (Std.Usize.wrapping_mul w 4#usize) =
      (w * 4#usize : Result Usize) := by
  have hsmall : w.val * 4 ≤ 32 := by omega
  have htry : (w * 4#usize : Result Usize) =
      .ok (small (w.val * 4) hsmall) := by
    change UScalar.tryMk .Usize (w.val * 4) = _
    exact try_small (w.val * 4) hsmall
  rw [htry]
  simp only [lift, Std.Usize.wrapping_mul]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [small_val, UScalar.wrapping_mul_val_eq, UScalar.size]
  change (w.val * 4) % (2 ^ System.Platform.numBits) = w.val * 4
  apply Nat.mod_eq_of_lt
  have hbound : w.val * 4 ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  exact UScalar.bound_suffices .Usize (w.val * 4) hbound

theorem wrapping_add_four_checked (w : Usize) (hw : w.val ≤ 28) :
    lift (Std.Usize.wrapping_add w 4#usize) =
      (w + 4#usize : Result Usize) := by
  have hsmall : w.val + 4 ≤ 32 := by omega
  have htry : (w + 4#usize : Result Usize) =
      .ok (small (w.val + 4) hsmall) := by
    change UScalar.tryMk .Usize (w.val + 4) = _
    exact try_small (w.val + 4) hsmall
  rw [htry]
  simp only [lift, Std.Usize.wrapping_add]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [small_val, UScalar.wrapping_add_val_eq, UScalar.size]
  change (w.val + 4) % (2 ^ System.Platform.numBits) = w.val + 4
  apply Nat.mod_eq_of_lt
  have hbound : w.val + 4 ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  exact UScalar.bound_suffices .Usize (w.val + 4) hbound

theorem wrapping_add_one_checked (w : Usize) (hw : w.val ≤ 8) :
    lift (Std.Usize.wrapping_add w 1#usize) =
      (w + 1#usize : Result Usize) := by
  have hsmall : w.val + 1 ≤ 32 := by omega
  have htry : (w + 1#usize : Result Usize) =
      .ok (small (w.val + 1) hsmall) := by
    change UScalar.tryMk .Usize (w.val + 1) = _
    exact try_small (w.val + 1) hsmall
  rw [htry]
  simp only [lift, Std.Usize.wrapping_add]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [small_val, UScalar.wrapping_add_val_eq, UScalar.size]
  change (w.val + 1) % (2 ^ System.Platform.numBits) = w.val + 1
  apply Nat.mod_eq_of_lt
  have hbound : w.val + 1 ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  exact UScalar.bound_suffices .Usize (w.val + 1) hbound

def sourceRead (b : Array U8 32#usize) (j : Usize) :
    Result (U32 × Usize) := do
  let i ← lift (Std.Usize.wrapping_mul j 4#usize)
  let i1 ← lift (Std.Usize.wrapping_mul j 4#usize)
  let i2 ← lift (Std.Usize.wrapping_add i1 4#usize)
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) b
    { start := i, «end» := i2 }
  let r ← core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s
  let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let word ← lift (core.num.U32.from_le_bytes a)
  let next ← lift (Std.Usize.wrapping_add j 1#usize)
  ok (word, next)

theorem sourceRead_eq_checked (b : Array U8 32#usize) (j : Usize)
    (hj : j.val < 8) :
    sourceRead b j = SamplerWordRead.read b j := by
  have hm := wrapping_mul_checked j (by omega)
  have hi : (small (j.val * 4) (by omega)).val ≤ 28 := by
    rw [small_val]
    omega
  have ha := wrapping_add_four_checked
    (small (j.val * 4) (by omega)) hi
  have hn := wrapping_add_one_checked j (by omega)
  have hchecked : (j * 4#usize : Result Usize) =
      .ok (small (j.val * 4) (by omega)) := by
    change UScalar.tryMk .Usize (j.val * 4) = _
    exact try_small _ _
  simp only [sourceRead, SamplerWordRead.read, hm, hchecked, bind_tc_ok,
    ha, hn]

theorem sourceRead_success (b : Array U8 32#usize) (j : Usize)
    (hj : j.val < 8) :
    sourceRead b j =
      .ok (core.num.U32.from_le_bytes
        (four b (j.val * 4) (by omega)),
        small (j.val + 1) (by omega)) := by
  rw [sourceRead_eq_checked b j hj]
  exact read_success b j hj

theorem mask_bound (word : U32) :
    (word &&& AspisR137Transcript.field.P).val ≤ 2147483647 := by
  change (word.bv &&& AspisR137Transcript.field.P.bv).toNat ≤ _
  rw [BitVec.toNat_and]
  simpa [AspisR137Transcript.field.P] using
    (Nat.and_le_right (n := word.bv.toNat)
      (m := AspisR137Transcript.field.P.bv.toNat))

theorem accepted_canonical (word : U32)
    (h : word &&& AspisR137Transcript.field.P ≠
      AspisR137Transcript.field.P) :
    (word &&& AspisR137Transcript.field.P).val < 2147483647 := by
  have hb := mask_bound word
  have hn : (word &&& AspisR137Transcript.field.P).val ≠ 2147483647 := by
    intro he
    apply h
    apply UScalar.eq_of_val_eq
    simpa [AspisR137Transcript.field.P] using he
  omega

#print axioms wrapping_mul_checked
#print axioms wrapping_add_four_checked
#print axioms wrapping_add_one_checked
#print axioms sourceRead_eq_checked
#print axioms sourceRead_success
#print axioms mask_bound
#print axioms accepted_canonical

end AspisV8R19.R137SamplerWordRead
