import V7CallerCurrentReleaseR26LineBatchLoop
import Mathlib.Data.Nat.BitIndices

/-!
# Current R26 line-batch query-weight semantics

This file identifies the bit-product computed by the generated line evaluator
with the exact natural-line basis used by the maintained K1 source model.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace V7CallerCurrentReleaseR26QueryWeightSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFactorLoop
open V7CallerCurrentReleaseR26LineBatchLoop

abbrev M31 := V7CallerCurrentReleaseR26.field.M31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

theorem lineFactor_eq_natRec (x : ExactM31) :
    ∀ coordinate,
      lineFactor x coordinate =
        Nat.rec x (fun _ factor => 2 * factor ^ 2 - 1) coordinate
  | 0 => rfl
  | coordinate + 1 => by
      rw [lineFactor, lineFactor_eq_natRec]

private theorem selectedLineBit_nonzero_iff_testBit
    (index : Std.U32) (coordinate : Nat) (coordinateBound : coordinate < 32) :
    (selectedLineBit index coordinate != 0#u32) = true ↔
      index.val.testBit coordinate = true := by
  have amountVal : (u32OfNatTruncate coordinate).val = coordinate :=
    by
      simp only [u32OfNatTruncate, UScalar.ofNatCore_val_eq]
      exact Nat.mod_eq_of_lt (lt_trans coordinateBound (by norm_num))
  have maskVal :
      (Std.U32.wrapping_shl 1#u32
        (u32OfNatTruncate coordinate)).val = 2 ^ coordinate := by
    unfold Std.U32.wrapping_shl UScalar.wrapping_shl
    change
      ((1#u32).bv.shiftLeft
        ((u32OfNatTruncate coordinate).val % 32)).toNat = 2 ^ coordinate
    unfold BitVec.shiftLeft
    have powBound : 2 ^ coordinate < 2 ^ 32 :=
      pow_lt_pow_right₀ (by norm_num) coordinateBound
    norm_num at powBound
    simp [amountVal, Nat.mod_eq_of_lt coordinateBound, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt powBound]
  have selectedVal :
      (selectedLineBit index coordinate).val =
        index.val &&& 2 ^ coordinate := by
    unfold selectedLineBit
    change
      index.val &&&
        (Std.U32.wrapping_shl 1#u32
          (u32OfNatTruncate coordinate)).val = _
    rw [maskVal]
  have selectedNeIff :
      selectedLineBit index coordinate ≠ 0#u32 ↔
        (selectedLineBit index coordinate).val ≠ 0 := by
    constructor
    · intro scalarNe valZero
      apply scalarNe
      apply UScalar.eq_of_val_eq
      simpa using valZero
    · intro valNe scalarZero
      apply valNe
      simp [scalarZero]
  rw [bne_iff_ne, selectedNeIff, selectedVal, Nat.and_two_pow]
  cases index.val.testBit coordinate <;> simp

def exactNaturalLineValue (x : ExactM31) (index : Nat) : ExactQM31 :=
  ∏ coordinate ∈ index.bitIndices.toFinset,
    (⟨⟨lineFactor x coordinate, 0⟩, 0⟩ : ExactQM31)

private theorem lineTerm_eq_testBit
    (x : M31) (index : Std.U32) (coordinate : Nat)
    (coordinateBound : coordinate < 32) :
    lineTerm x index coordinate =
      if index.val.testBit coordinate = true then
        (⟨⟨lineFactor (generatedM31ToExact x) coordinate, 0⟩, 0⟩ :
          ExactQM31)
      else 1 := by
  unfold lineTerm
  have selectedIff :=
    selectedLineBit_nonzero_iff_testBit index coordinate coordinateBound
  by_cases selected : index.val.testBit coordinate = true
  · have generatedSelected :
        (selectedLineBit index coordinate != 0#u32) = true :=
      selectedIff.2 selected
    simp [selected, generatedSelected]
  · have generatedUnselected :
        ¬ (selectedLineBit index coordinate != 0#u32) = true :=
      fun generatedSelected => selected (selectedIff.1 generatedSelected)
    simp [selected, generatedUnselected]

private theorem bitIndices_support_eq
    (index width : Nat) (indexBound : index < 2 ^ width) :
    (Finset.range width).filter (fun coordinate =>
      index.testBit coordinate = true) = index.bitIndices.toFinset := by
  ext coordinate
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset,
    Nat.mem_bitIndices]
  constructor
  · exact fun condition => condition.2
  · intro selected
    refine ⟨?_, selected⟩
    have selectedPower : 2 ^ coordinate ≤ index :=
      Nat.two_pow_le_of_mem_bitIndices ((Nat.mem_bitIndices).2 selected)
    by_contra outside
    have widthLe : width ≤ coordinate := by omega
    have powerLe : 2 ^ width ≤ 2 ^ coordinate :=
      pow_le_pow_right₀ (by norm_num) widthLe
    omega

/-- Below the supplied bit width, the generated selected-factor product is
exactly the natural-line product indexed by the set bits of the coefficient. -/
theorem line_product_eq_exactNaturalLineValue
    (x : M31) (index : Std.U32) (width : Nat)
    (widthBound : width ≤ 32) (indexBound : index.val < 2 ^ width) :
    ∏ coordinate ∈ Finset.range width, lineTerm x index coordinate =
      exactNaturalLineValue (generatedM31ToExact x) index.val := by
  classical
  calc
    ∏ coordinate ∈ Finset.range width, lineTerm x index coordinate =
        ∏ coordinate ∈ Finset.range width,
          if index.val.testBit coordinate = true then
            (⟨⟨lineFactor (generatedM31ToExact x) coordinate, 0⟩, 0⟩ :
              ExactQM31)
          else 1 := by
            apply Finset.prod_congr rfl
            intro coordinate member
            apply lineTerm_eq_testBit
            have := Finset.mem_range.1 member
            omega
    _ = ∏ coordinate ∈
          (Finset.range width).filter (fun coordinate =>
            index.val.testBit coordinate = true),
          (⟨⟨lineFactor (generatedM31ToExact x) coordinate, 0⟩, 0⟩ :
            ExactQM31) := by
          symm
          apply Finset.prod_filter
    _ = exactNaturalLineValue (generatedM31ToExact x) index.val := by
          rw [bitIndices_support_eq index.val width indexBound]
          rfl

#print axioms line_product_eq_exactNaturalLineValue

theorem linePrefix_eq_exactNaturalLineValue
    (scale : V7CallerCurrentReleaseR26.field.QM31) (x : M31)
    (index : Std.U32) (width : Nat)
    (widthBound : width ≤ 32) (indexBound : index.val < 2 ^ width) :
    linePrefix scale x index width =
      generatedQm31ToExact scale *
        exactNaturalLineValue (generatedM31ToExact x) index.val := by
  unfold linePrefix
  rw [line_product_eq_exactNaturalLineValue x index width widthBound indexBound]

def exactShiftedLineBatchWeight (rho : ExactQM31)
    (lineX : Nat → ExactM31) (coefficient : Nat) : ExactQM31 :=
  ∑ ordinal ∈ Finset.range 16,
    rho ^ (ordinal + 1) * exactNaturalLineValue (lineX ordinal) coefficient

/-- For the fixed Tag-73 dimensions, exact shifted powers and exact line
coordinates turn the generated batch prefix into the K1-shaped ordered
sixteen-query covector. -/
theorem lineBatchPrefix_eq_exactShiftedLineBatchWeight
    (logLen : Std.U32)
    (scales : Slice V7CallerCurrentReleaseR26.field.QM31)
    (xs : Slice M31) (index : Std.U32)
    (rho : ExactQM31) (lineX : Nat → ExactM31)
    (logLenExact : logLen.val = 18)
    (scalesLength : scales.length = 16)
    (scaleExact : ∀ ordinal, ordinal < 16 →
      generatedQm31ToExact scales.val[ordinal]! = rho ^ (ordinal + 1))
    (lineXExact : ∀ ordinal, ordinal < 16 →
      generatedM31ToExact xs.val[ordinal]! = lineX ordinal)
    (coefficientBound : index.val < 256) :
    lineBatchPrefix logLen scales xs index scales.length =
      exactShiftedLineBatchWeight rho lineX index.val := by
  classical
  rw [scalesLength]
  unfold lineBatchPrefix exactShiftedLineBatchWeight
  apply Finset.sum_congr rfl
  intro ordinal member
  have ordinalBound : ordinal < 16 := Finset.mem_range.1 member
  unfold lineBatchTerm
  rw [linePrefix_eq_exactNaturalLineValue]
  · rw [scaleExact ordinal ordinalBound,
      lineXExact ordinal ordinalBound]
  · omega
  · rw [logLenExact]
    have coefficientSmall : index.val < 2 ^ 18 := by omega
    exact coefficientSmall

#print axioms lineBatchPrefix_eq_exactShiftedLineBatchWeight

end V7CallerCurrentReleaseR26QueryWeightSemantics
