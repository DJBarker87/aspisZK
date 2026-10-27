import RPv_ArrayFromFnCopyStable
import RPv_RawPoseidonExternalRowWrapperSlice
import RPv_RawPoseidonExternalAllRows
import RPv_RawPoseidonExternalRowReads
import ExtractedMaskHornerStep
import RPv_RawPoseidonExtensionWords

/-! Component contract for the exact generated width-four row wrapper. It
composes the generated from_fn copy wrapper with the already-proved four-lane
callback facts and extension-word conversion. It is not a permutation or
terminal theorem. -/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalRowWrapper

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.RawPoseidonExternalAllRows
open AspisR1.RawPoseidonExtensionWords
open AspisR1.RawPoseidonExternalRows
open AspisR1.ExtractedMaskTowerAdd

abbrev Input := AspisR1.RawPoseidonExternalRowClosure.Input

private theorem small_nat_usize (n : Nat) (hn : n < 4) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 4 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

private def toUsize4 (i : Fin 4) : Usize :=
  Usize.ofNatCore i.val (small_nat_usize i.val i.isLt)

private theorem toUsize4_val (i : Fin 4) : (toUsize4 i).val = i.val := by
  simp [toUsize4, UScalar.ofNatCore_val_eq]

private theorem toUsize4_eq (i : Fin 4) (x : Usize) (hx : x.val = i.val) :
    toUsize4 i = x := by
  apply UScalar.eq_of_val_eq
  simp [toUsize4_val, hx]

/-- The exact Nat row formula used by G's callback at one input limb. -/
def rawRowFormula (input : Input) (output : Fin 4) (limb : Usize)
    (hlimb : limb.val < 4) : Nat :=
  RawPoseidonExternalRows.rawRowNat
    (fun r : Fin 4 => (RawPoseidonExternalRowReads.limbValue input r limb hlimb).val)
    output

theorem rawRowFormula_bound (input : Input) (output : Fin 4)
    (limb : Usize) (hlimb : limb.val < 4) :
    rawRowFormula input output limb hlimb < 2^35 := by
  apply RawPoseidonExternalRows.rawRowNat_lt_two_pow_35
  intro r
  exact (RawPoseidonExternalRowReads.limbValue input r limb hlimb).bv.isLt

private theorem callback_value
    (input : Input) (output : Fin 4) (limb : Usize) (hlimb : limb.val < 4) :
    ∃ z : U64,
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (input, toUsize4 output) limb = .ok (z, (input, toUsize4 output)) ∧
      z.val = rawRowFormula input output limb hlimb := by
  obtain ⟨z0, z1, z2, z3, hc0, hv0, hc1, hv1, hc2, hv2, hc3, hv3⟩ :=
    call_mut_all_lanes_of_array_bounds input limb hlimb
  fin_cases output
  · have ho : toUsize4 (⟨0, by decide⟩ : Fin 4) = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z0, ?_, ?_⟩
    · rw [ho]
      exact hc0
    · simpa [rawRowFormula, RawPoseidonExternalRows.rawRowNat,
      RawPoseidonExternalRowReads.rawRowNat] using hv0
  · have ho : toUsize4 (⟨1, by decide⟩ : Fin 4) = 1#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z1, ?_, ?_⟩
    · rw [ho]
      exact hc1
    · simpa [rawRowFormula, RawPoseidonExternalRows.rawRowNat,
      RawPoseidonExternalRowReads.rawRowNat] using hv1
  · have ho : toUsize4 (⟨2, by decide⟩ : Fin 4) = 2#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z2, ?_, ?_⟩
    · rw [ho]
      exact hc2
    · simpa [rawRowFormula, RawPoseidonExternalRows.rawRowNat,
      RawPoseidonExternalRowReads.rawRowNat] using hv2
  · have ho : toUsize4 (⟨3, by decide⟩ : Fin 4) = 3#usize := by
      apply UScalar.eq_of_val_eq
      simp [toUsize4_val]
    refine ⟨z3, ?_, ?_⟩
    · rw [ho]
      exact hc3
    · simpa [rawRowFormula, RawPoseidonExternalRows.rawRowNat,
      RawPoseidonExternalRowReads.rawRowNat] using hv3

private def callbackValue (input : Input) (output : Fin 4) (n : Nat) : U64 :=
  if hn : n < 4 then
    let limb := toUsize4 ⟨n, hn⟩
    let hl : limb.val < 4 := by simpa [limb, toUsize4_val] using hn
    U64.ofNatCore (rawRowFormula input output limb hl) (by
      have h := rawRowFormula_bound input output limb hl
      simp only [UScalarTy.U64_numBits_eq]
      omega)
  else 0#u64

theorem external_linear_lazy_row_words
    (input : Input) (output : Fin 4) :
    ∃ raw : Array U64 4#usize, ∃ q : field.QM31,
      state_only_poseidon.external_linear_lazy_row input (toUsize4 output) = .ok q ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q ∧
      wordsQM q =
        (((raw.val[0]'(by simpa [raw.property] using (show 0 < 4 by decide))).val % P,
           (raw.val[1]'(by simpa [raw.property] using (show 1 < 4 by decide))).val % P),
          ((raw.val[2]'(by simpa [raw.property] using (show 2 < 4 by decide))).val % P,
           (raw.val[3]'(by simpa [raw.property] using (show 3 < 4 by decide))).val % P)) ∧
      (∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
          rawRowFormula input output (toUsize4 j)
            (show (toUsize4 j).val < 4 by simpa [toUsize4_val] using j.isLt)) := by
  let inst := state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  let value : Nat → U64 := callbackValue input output
  have hstable : ∀ i : Usize, i.val < 4 →
      inst.call_mut (input, toUsize4 output) i =
        .ok (value i.val, (input, toUsize4 output)) := by
    intro i hi
    let ix : Fin 4 := ⟨i.val, hi⟩
    have hix : toUsize4 ix = i := toUsize4_eq ix i rfl
    obtain ⟨z, hcall, hz⟩ := callback_value input output i hi
    have hv : value i.val = z := by
      dsimp [value, callbackValue]
      rw [dif_pos hi]
      apply UScalar.eq_of_val_eq
      have hz' : rawRowFormula input output (toUsize4 ix)
          (by simpa [toUsize4_val] using hi) = z.val := by
        simpa only [hix] using hz.symm
      simpa only [U64.ofNatCore_val_eq] using hz'
    simpa [inst, hv] using hcall
  obtain ⟨raw, hrun, hcells⟩ :=
    AspisR1SelectedMaskProbe.array_from_fn_copy_stable
      (4#usize) core.marker.CopyU64 inst 0#u64 (input, toUsize4 output)
      value hstable
  obtain ⟨q, hconvert, hcanonical, hwords⟩ :=
    RawPoseidonExtensionWords.extension_from_raw_limbs_words raw
  have hrawFormula : ∀ j : Fin 4,
      (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
        rawRowFormula input output (toUsize4 j)
          (by simpa [toUsize4_val] using j.isLt) := by
    intro j
    have hj : j.val < 4 := j.isLt
    have hout := hcells j.val (by simpa using hj)
    have hvalue : value j.val =
        U64.ofNatCore (rawRowFormula input output (toUsize4 j)
          (by simpa [toUsize4_val] using hj)) (by
            have h := rawRowFormula_bound input output (toUsize4 j)
              (by simpa [toUsize4_val] using hj)
            simp only [UScalarTy.U64_numBits_eq]
            omega) := by
      apply UScalar.eq_of_val_eq
      dsimp [value, callbackValue]
      rw [dif_pos hj]
    rw [hvalue] at hout
    have hval := congrArg UScalar.val hout
    simpa only [U64.ofNatCore_val_eq] using hval
  refine ⟨raw, q, ?_, hcanonical, ?_, ?_⟩
  · change (do
      let raw1 ← array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (input, toUsize4 output)
      state_only_poseidon.extension_from_raw_limbs raw1) = .ok q
    rw [hrun]
    exact hconvert
  · simpa [wordsQM, RawPoseidonExtensionWords.limbAt] using hwords
  · intro j
    exact hrawFormula j

#print axioms callback_value
#print axioms external_linear_lazy_row_words
end AspisR1.RawPoseidonExternalRowWrapper
