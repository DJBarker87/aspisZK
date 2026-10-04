import AspisR614SelectedCombineBeta.Funs
import AspisV8R19.GeneratedInverseLoop
import AspisV8R19.SamplerWordRead
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

def sourceIndex (slot : U4) : Usize :=
  SamplerWordRead.small slot.val (by omega)

def nextSourceIndex (slot : U4) : Usize :=
  SamplerWordRead.small (slot.val + 1) (by omega)

def laneRow (lane : U4 → U4 → U32) (slot : U4) : AspisR614SelectedCombineBeta.aspis_core.field.QM31 :=
  { c0 := { a := lane slot 0, b := lane slot 1 },
    c1 := { a := lane slot 2, b := lane slot 3 } }

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

theorem sourceC1Chunk_bind {β : Type} (c1 : Std.Array U32 104#usize)
    (slot : Usize) (k : Std.Array U32 26#usize → Result β) :
    (do
      let i ← lift (Usize.wrapping_mul 26#usize slot)
      let i1 ← lift (Usize.wrapping_add slot 1#usize)
      let i2 ← lift (Usize.wrapping_mul 26#usize i1)
      let s ← core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U32))
        c1 { start := i, «end» := i2 }
      let r ← core.array.TryFromSharedArraySlice.try_from 26#usize s
      let values ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      k values) = (do let values ← sourceC1Chunk c1 slot; k values) := by
  simp [sourceC1Chunk, bind_assoc_eq]

theorem sourceC1Chunk_ok (c1 : Std.Array U32 104#usize) (n : Nat) (hn : n < 4) :
    sourceC1Chunk c1 (UScalar.ofNatCore n (by
      have hmax := Usize.cMax_bound
      have hbits := Usize.size
      scalar_tac)) = .ok (c1Chunk c1 ⟨n, hn⟩) := by
  interval_cases n
  all_goals
    have hsize : 200 < Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        simp [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq, hp] <;> omega
    have hmod0 : 0 % Usize.size = 0 := Nat.mod_eq_of_lt (by omega)
    have hmod26 : 26 % Usize.size = 26 := Nat.mod_eq_of_lt (by omega)
    have hmod52 : 52 % Usize.size = 52 := Nat.mod_eq_of_lt (by omega)
    have hmod78 : 78 % Usize.size = 78 := Nat.mod_eq_of_lt (by omega)
    have hmod104 : 104 % Usize.size = 104 := Nat.mod_eq_of_lt (by omega)
    have hmul0 : Usize.wrapping_mul 26#usize 0#usize = 0#usize := by
      exact wrapping_mul_ofNat 26 0 (by omega) (by omega) (by omega)
    have hmul1 : Usize.wrapping_mul 26#usize 1#usize = 26#usize := by
      exact wrapping_mul_ofNat 26 1 (by omega) (by omega) (by omega)
    have hmul2 : Usize.wrapping_mul 26#usize 2#usize = 52#usize := by
      exact wrapping_mul_ofNat 26 2 (by omega) (by omega) (by omega)
    have hmul3 : Usize.wrapping_mul 26#usize 3#usize = 78#usize := by
      exact wrapping_mul_ofNat 26 3 (by omega) (by omega) (by omega)
    have hmul4 : Usize.wrapping_mul 26#usize 4#usize = 104#usize := by
      exact wrapping_mul_ofNat 26 4 (by omega) (by omega) (by omega)
    have hadd01 : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
      exact wrapping_add_ofNat 0 1 (by omega) (by omega) (by omega)
    have hadd12 : Usize.wrapping_add 1#usize 1#usize = 2#usize := by
      exact wrapping_add_ofNat 1 1 (by omega) (by omega) (by omega)
    have hadd23 : Usize.wrapping_add 2#usize 1#usize = 3#usize := by
      exact wrapping_add_ofNat 2 1 (by omega) (by omega) (by omega)
    have hadd34 : Usize.wrapping_add 3#usize 1#usize = 4#usize := by
      exact wrapping_add_ofNat 3 1 (by omega) (by omega) (by omega)
    have hc1len : c1.val.length = 104 := by
      have h := c1.property
      have hu : (104#usize : Usize).val = 104 := by scalar_tac
      simpa only [hu] using h
    have hu26 : Usize.ofNatCore 26 (by have hc := Usize.cMax_bound; scalar_tac) =
        (26#usize : Usize) := by rfl
    simp [sourceC1Chunk, core.array.Array.index, core.ops.index.IndexSlice,
      core.slice.index.SliceIndexRangeUsizeSlice, core.array.TryFromSharedArraySlice.try_from,
      core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv,
      core.result.Result.unwrap, Array.to_slice, Slice.length, Slice.len, List.slice,
      List.length_take, List.length_drop, hc1len,
      c1Chunk, Array.make, lift,
      hsize, hmod0, hmod26, hmod52, hmod78, hmod104,
      hu26,
      hmul0, hmul1, hmul2, hmul3, hmul4, hadd01, hadd12, hadd23, hadd34]
    <;> omega

theorem combine_beta_body_slot
    (powers : query_arithmetic.BetaCoefficients)
    (c1 : Std.Array U32 104#usize) (c2 : Std.Array U32 48#usize)
    (out : Std.Array aspis_core.field.QM31 4#usize)
    (lane : U4 → U4 → U32)
    (hleaf : ∀ (slot : U4) (limb : U4),
      query_arithmetic.r83_mixed_limb (UScalar.ofNatCore limb.val
        (by have h := Usize.cMax_bound; scalar_tac))
        (c1Chunk c1 slot) c2 (sourceIndex slot) powers = .ok (lane slot limb))
    (slot : U4) :
    query_arithmetic.combine_beta_loop.body powers c1 c2
      { start := sourceIndex slot, «end» := 4#usize } out =
      (do
        let out1 ← Array.update out (sourceIndex slot) (laneRow lane slot)
        ok (.cont ({ start := nextSourceIndex slot, «end» := 4#usize }, out1))) := by
  have hsource_val : (sourceIndex slot).val = slot.val :=
    SamplerWordRead.small_val _ _
  have hnext_val : (nextSourceIndex slot).val = slot.val + 1 :=
    SamplerWordRead.small_val _ _
  have hlt : (sourceIndex slot).val < (4#usize : Usize).val := by
    simp only [hsource_val, UScalar.ofNatCore_val_eq]
    omega
  have hnext : Usize.wrapping_add (sourceIndex slot) 1#usize = nextSourceIndex slot := by
    simpa [sourceIndex, nextSourceIndex, SamplerWordRead.small] using
      wrapping_add_ofNat slot.val 1 (by omega) (by norm_num) (by omega)
  have hiter_next : UScalar.ofNatCore ((sourceIndex slot).val + 1)
      (by have h := Usize.cMax_bound; scalar_tac) = nextSourceIndex slot := by
    simp [sourceIndex, nextSourceIndex, SamplerWordRead.small, hsource_val]
  have hchunk : sourceC1Chunk c1 (sourceIndex slot) = .ok (c1Chunk c1 slot) := by
    simpa [sourceIndex, SamplerWordRead.small] using
      sourceC1Chunk_ok c1 slot.val slot.isLt
  have hrange := GeneratedInverseLoop.range_next
    ({ start := sourceIndex slot, «end» := 4#usize } : core.ops.range.Range Usize)
  rw [query_arithmetic.combine_beta_loop.body, hrange]
  simp only [dif_pos hlt, bind_tc_ok]
  rw [sourceC1Chunk_bind, hchunk]
  simp [hleaf, laneRow, Array.index_usize, Array.make, Array.update,
    aspis_core.field.CM31.new, hiter_next]

end AspisR614SelectedCombineBeta

end AspisV8R19.R646CombineLoopExecution
