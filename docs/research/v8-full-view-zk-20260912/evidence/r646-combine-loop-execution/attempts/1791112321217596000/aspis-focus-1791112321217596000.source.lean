import AspisR614SelectedCombineBeta.Funs
import AspisV8R19.GeneratedInverseLoop
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R646CombineLoopExecution

open Aeneas Aeneas.Std Result ControlFlow
open AspisR614SelectedCombineBeta

private abbrev U4 := Fin 4

/-- The selected 26-word C1 chunk, expressed as the exact drop/take slice. -/
def c1Chunk (c1 : Array U32 104#usize) (slot : U4) : Array U32 26#usize :=
  Array.make 26#usize (c1.val.drop (26 * slot.val) |>.take 26) (by
    have hlen : c1.val.length = 104 := by
      have h := c1.property
      have hu : (104#usize : Usize).val = 104 := by scalar_tac
      simpa only [hu] using h
    rw [List.length_take, List.length_drop, hlen]
    have hbound : 26 ≤ 104 - 26 * slot.val := by omega
    rw [Nat.min_eq_left hbound]
    have h26 : (26#usize : Usize).val = 26 := by scalar_tac
    simpa only [h26])

lemma c1Chunk_val (c1 : Array U32 104#usize) (slot : U4) :
    (c1Chunk c1 slot).val = (c1.val.drop (26 * slot.val)).take 26 := rfl

namespace AspisR614SelectedCombineBeta

open AspisV8R19.R646CombineLoopExecution

private def smallUsize (n : Nat) (hn : n < 200) : Usize :=
  UScalar.ofNatCore n (by have hc := Usize.cMax_bound; scalar_tac)

private theorem wrapping_mul_small (a b : Nat) (ha : a < 200) (hb : b < 200)
    (hab : a * b < 200) :
    Usize.wrapping_mul (smallUsize a ha) (smallUsize b hb) = smallUsize (a*b) hab := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_mul, UScalar.wrapping_mul_val_eq,
    smallUsize, UScalar.ofNatCore_val_eq]
  have hlt : a * b < UScalar.size .Usize := by
    rcases System.Platform.numBits_eq with hp | hp <;>
      simp [UScalar.size, Usize.size, Usize.numBits,
        UScalarTy.Usize_numBits_eq, hp] <;> omega
  rw [Nat.mod_eq_of_lt hlt]

private theorem wrapping_add_small (a b : Nat) (ha : a < 200) (hb : b < 200)
    (hab : a + b < 200) :
    Usize.wrapping_add (smallUsize a ha) (smallUsize b hb) = smallUsize (a+b) hab := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add, UScalar.wrapping_add_val_eq,
    smallUsize, UScalar.ofNatCore_val_eq]
  have hlt : a + b < UScalar.size .Usize := by
    rcases System.Platform.numBits_eq with hp | hp <;>
      simp [UScalar.size, Usize.size, Usize.numBits,
        UScalarTy.Usize_numBits_eq, hp] <;> omega
  rw [Nat.mod_eq_of_lt hlt]

private theorem wrapping_mul_ofNat (a b : Nat) (ha : a < 200) (hb : b < 200)
    (hab : a*b < 200) :
    Usize.wrapping_mul (UScalar.ofNatCore a (by have hc := Usize.cMax_bound; scalar_tac))
      (UScalar.ofNatCore b (by have hc := Usize.cMax_bound; scalar_tac)) =
    UScalar.ofNatCore (a*b) (by have hc := Usize.cMax_bound; scalar_tac) := by
  simpa [smallUsize] using wrapping_mul_small a b ha hb hab

private theorem wrapping_add_ofNat (a b : Nat) (ha : a < 200) (hb : b < 200)
    (hab : a+b < 200) :
    Usize.wrapping_add (UScalar.ofNatCore a (by have hc := Usize.cMax_bound; scalar_tac))
      (UScalar.ofNatCore b (by have hc := Usize.cMax_bound; scalar_tac)) =
    UScalar.ofNatCore (a+b) (by have hc := Usize.cMax_bound; scalar_tac) := by
  simpa [smallUsize] using wrapping_add_small a b ha hb hab

def sourceC1Chunk (c1 : Std.Array U32 104#usize) (slot : Usize) : Result (Std.Array U32 26#usize) := do
  let i ← lift (Usize.wrapping_mul 26#usize slot)
  let i1 ← lift (Usize.wrapping_add slot 1#usize)
  let i2 ← lift (Usize.wrapping_mul 26#usize i1)
  let s ← core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U32))
    c1 { start := i, «end» := i2 }
  let r ← core.array.TryFromSharedArraySlice.try_from 26#usize s
  let values ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  .ok values

theorem sourceC1Chunk_ok (c1 : Std.Array U32 104#usize) (n : Nat) (hn : n < 4) :
    sourceC1Chunk c1 (UScalar.ofNatCore n (by
      have hmax := Usize.cMax_bound
      have hbits := Usize.size
      scalar_tac)) = .ok (c1Chunk c1 ⟨n, hn⟩) := by
  interval_cases n
  all_goals
    have hmul1 := wrapping_mul_ofNat 26 n (by norm_num) (by omega) (by omega)
    have hadd := wrapping_add_ofNat n 1 (by omega) (by norm_num) (by omega)
    have hmul2 := wrapping_mul_ofNat 26 (n+1) (by norm_num) (by omega) (by omega)
    simp [sourceC1Chunk, core.array.Array.index, core.ops.index.IndexSlice,
      core.slice.index.SliceIndexRangeUsizeSlice, core.array.TryFromSharedArraySlice.try_from,
      core.result.Result.unwrap, Array.to_slice, c1Chunk, Array.make, lift,
      hmul1, hadd, hmul2]

end AspisR614SelectedCombineBeta

end AspisV8R19.R646CombineLoopExecution
