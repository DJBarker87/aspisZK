import V7CallerCurrentReleaseR26GroupedRowsTwiceTrace

/-!
# Exact generated basis for the optimized grouped two-fold helper

The optimized source forms the tensor product of the two arity-four fold
bases.  This module exposes all nine nontrivial generated multiplications and
the exact ordered sixteen-entry array returned by `array::from_fn`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceBasis

open V7CallerCurrentReleaseR26GroupedRowsTwiceTrace
open V7CallerCurrentReleaseR26FieldBridge

abbrev RawQM31 := field.QM31

private def basisClosure
    (alpha1 alpha2 alpha1Squared alpha2Squared alpha1Cubed alpha2Cubed :
      RawQM31) : sumcheck.fold_grouped_rows_twice.closure :=
  (Array.make 4#usize
      [field.QM31.ONE, alpha1Cubed, alpha1Squared, alpha1],
   Array.make 4#usize
      [field.QM31.ONE, alpha2Cubed, alpha2Squared, alpha2])

private theorem usizeShrTwoVal (low : Std.Usize) :
    (Std.Usize.wrapping_shr low 2#u32).val = low.val >>> 2 := by
  change (Std.Usize.wrapping_shr low 2#u32).bv.toNat =
    low.bv.toNat >>> 2
  rw [Std.Usize.wrapping_shr_bv_eq]
  have hshift : (2#u32).val % System.Platform.numBits = 2 := by
    cases System.Platform.numBits_eq <;> simp_all
  rw [hshift]
  change (low.bv >>> (2 : Nat)).toNat = low.bv.toNat >>> 2
  rw [BitVec.toNat_ushiftRight]

private theorem usizeShrTwoExact (low high : Std.Usize)
    (valueExact : low.val >>> 2 = high.val) :
    Std.Usize.wrapping_shr low 2#u32 = high := by
  apply UScalar.val_eq_imp
  rw [usizeShrTwoVal]
  exact valueExact

private theorem usizeAddOneOk (low next : Std.Usize)
    (valueExact : low.val + 1 = next.val) :
    low + 1#usize = (ok next : Result Std.Usize) := by
  have bound : low.val + 1 < 2 ^ System.Platform.numBits := by
    rw [valueExact]
    exact next.hBounds
  have addSpec := @UScalar.add_equiv UScalarTy.Usize low 1#usize
  generalize runEq : (low + 1#usize) = result at addSpec ⊢
  cases result with
  | fail error =>
      exfalso
      apply addSpec
      simpa using bound
  | div => exact False.elim addSpec
  | ok value =>
      have sameValue : value.val = next.val := by
        calc
          value.val = low.val + (1#usize).val := addSpec.2.1
          _ = low.val + 1 := by rfl
          _ = next.val := valueExact
      have : value = next := UScalar.val_eq_imp value next sameValue
      simp [this]

private theorem basisCallbackHighZero
    (closure : sumcheck.fold_grouped_rows_twice.closure)
    (index low : Std.Usize) (value : RawQM31)
    (highRun : Std.Usize.wrapping_shr index 2#u32 = 0#usize)
    (lowRun : index &&& 3#usize = low)
    (readRun : Array.index_usize closure.1 low = ok value) :
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        closure index = ok (value, closure) := by
  rcases closure with ⟨first, second⟩
  unfold
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [Std.lift, bind_tc_ok]
  rw [highRun, lowRun]
  simp only [ite_true, readRun, bind_tc_ok]

private theorem basisCallbackLowZero
    (closure : sumcheck.fold_grouped_rows_twice.closure)
    (index high : Std.Usize) (value : RawQM31)
    (highRun : Std.Usize.wrapping_shr index 2#u32 = high)
    (highNonzero : high ≠ 0#usize)
    (lowRun : index &&& 3#usize = 0#usize)
    (readRun : Array.index_usize closure.2 high = ok value) :
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        closure index = ok (value, closure) := by
  rcases closure with ⟨first, second⟩
  unfold
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [Std.lift, bind_tc_ok]
  rw [highRun, lowRun]
  simp only [if_neg highNonzero, ite_true, readRun, bind_tc_ok]

private theorem basisCallbackCross
    (closure : sumcheck.fold_grouped_rows_twice.closure)
    (index high low : Std.Usize) (left right product : RawQM31)
    (highRun : Std.Usize.wrapping_shr index 2#u32 = high)
    (highNonzero : high ≠ 0#usize)
    (lowRun : index &&& 3#usize = low)
    (lowNonzero : low ≠ 0#usize)
    (leftRun : Array.index_usize closure.2 high = ok left)
    (rightRun : Array.index_usize closure.1 low = ok right)
    (mulRun : field.QM31.mul left right = ok product) :
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        closure index = ok (product, closure) := by
  rcases closure with ⟨first, second⟩
  unfold
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [Std.lift, bind_tc_ok]
  rw [highRun, lowRun]
  simp only [if_neg highNonzero, if_neg lowNonzero, leftRun, rightRun,
    bind_tc_ok, mulRun]

structure GroupedRowsTwiceBasisTrace
    (alpha1 alpha2 alpha1Squared alpha2Squared alpha1Cubed alpha2Cubed :
      RawQM31)
    (basis : Array RawQM31 16#usize) : Type where
  b5 : RawQM31
  b6 : RawQM31
  b7 : RawQM31
  b9 : RawQM31
  b10 : RawQM31
  b11 : RawQM31
  b13 : RawQM31
  b14 : RawQM31
  b15 : RawQM31
  b5Run : field.QM31.mul alpha2Cubed alpha1Cubed = ok b5
  b6Run : field.QM31.mul alpha2Cubed alpha1Squared = ok b6
  b7Run : field.QM31.mul alpha2Cubed alpha1 = ok b7
  b9Run : field.QM31.mul alpha2Squared alpha1Cubed = ok b9
  b10Run : field.QM31.mul alpha2Squared alpha1Squared = ok b10
  b11Run : field.QM31.mul alpha2Squared alpha1 = ok b11
  b13Run : field.QM31.mul alpha2 alpha1Cubed = ok b13
  b14Run : field.QM31.mul alpha2 alpha1Squared = ok b14
  b15Run : field.QM31.mul alpha2 alpha1 = ok b15
  outputExact : basis = Array.make 16#usize
    [field.QM31.ONE, alpha1Cubed, alpha1Squared, alpha1,
     alpha2Cubed, b5, b6, b7,
     alpha2Squared, b9, b10, b11,
     alpha2, b13, b14, b15]

theorem generated_basis_exposes_tensor_entries
    (alpha1 alpha2 alpha1Squared alpha2Squared alpha1Cubed alpha2Cubed :
      RawQM31)
    (basis : Array RawQM31 16#usize)
    (alpha1Canonical : GeneratedCanonicalQM31 alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha1SquaredCanonical : GeneratedCanonicalQM31 alpha1Squared)
    (alpha2SquaredCanonical : GeneratedCanonicalQM31 alpha2Squared)
    (alpha1CubedCanonical : GeneratedCanonicalQM31 alpha1Cubed)
    (alpha2CubedCanonical : GeneratedCanonicalQM31 alpha2Cubed)
    (run : core.array.from_fn 16#usize
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      (Array.make 4#usize
        [field.QM31.ONE, alpha1Cubed, alpha1Squared, alpha1],
       Array.make 4#usize
        [field.QM31.ONE, alpha2Cubed, alpha2Squared, alpha2]) = ok basis) :
    Nonempty (GroupedRowsTwiceBasisTrace alpha1 alpha2 alpha1Squared
      alpha2Squared alpha1Cubed alpha2Cubed basis) := by
  obtain ⟨b5, h5, _, _⟩ := generated_qm31_mul_corresponds
    alpha2Cubed alpha1Cubed alpha2CubedCanonical alpha1CubedCanonical
  obtain ⟨b6, h6, _, _⟩ := generated_qm31_mul_corresponds
    alpha2Cubed alpha1Squared alpha2CubedCanonical alpha1SquaredCanonical
  obtain ⟨b7, h7, _, _⟩ := generated_qm31_mul_corresponds
    alpha2Cubed alpha1 alpha2CubedCanonical alpha1Canonical
  obtain ⟨b9, h9, _, _⟩ := generated_qm31_mul_corresponds
    alpha2Squared alpha1Cubed alpha2SquaredCanonical alpha1CubedCanonical
  obtain ⟨b10, h10, _, _⟩ := generated_qm31_mul_corresponds
    alpha2Squared alpha1Squared alpha2SquaredCanonical alpha1SquaredCanonical
  obtain ⟨b11, h11, _, _⟩ := generated_qm31_mul_corresponds
    alpha2Squared alpha1 alpha2SquaredCanonical alpha1Canonical
  obtain ⟨b13, h13, _, _⟩ := generated_qm31_mul_corresponds
    alpha2 alpha1Cubed alpha2Canonical alpha1CubedCanonical
  obtain ⟨b14, h14, _, _⟩ := generated_qm31_mul_corresponds
    alpha2 alpha1Squared alpha2Canonical alpha1SquaredCanonical
  obtain ⟨b15, h15, _, _⟩ := generated_qm31_mul_corresponds
    alpha2 alpha1 alpha2Canonical alpha1Canonical
  let closure := basisClosure alpha1 alpha2 alpha1Squared alpha2Squared
    alpha1Cubed alpha2Cubed
  have call0 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 0#usize = ok (field.QM31.ONE, closure) := by
    apply basisCallbackHighZero closure 0#usize 0#usize field.QM31.ONE
      (usizeShrTwoExact 0#usize 0#usize rfl) (by decide)
    rfl
  have call1 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 1#usize = ok (alpha1Cubed, closure) := by
    apply basisCallbackHighZero closure 1#usize 1#usize alpha1Cubed
      (usizeShrTwoExact 1#usize 0#usize rfl) (by decide)
    rfl
  have call2 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 2#usize = ok (alpha1Squared, closure) := by
    apply basisCallbackHighZero closure 2#usize 2#usize alpha1Squared
      (usizeShrTwoExact 2#usize 0#usize rfl) (by decide)
    rfl
  have call3 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 3#usize = ok (alpha1, closure) := by
    apply basisCallbackHighZero closure 3#usize 3#usize alpha1
      (usizeShrTwoExact 3#usize 0#usize rfl) (by decide)
    rfl
  have call4 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 4#usize = ok (alpha2Cubed, closure) := by
    apply basisCallbackLowZero closure 4#usize 1#usize alpha2Cubed
      (usizeShrTwoExact 4#usize 1#usize rfl) (by decide) (by decide)
    rfl
  have call5 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 5#usize = ok (b5, closure) := by
    apply basisCallbackCross closure 5#usize 1#usize 1#usize
      alpha2Cubed alpha1Cubed b5
      (usizeShrTwoExact 5#usize 1#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h5
  have call6 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 6#usize = ok (b6, closure) := by
    apply basisCallbackCross closure 6#usize 1#usize 2#usize
      alpha2Cubed alpha1Squared b6
      (usizeShrTwoExact 6#usize 1#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h6
  have call7 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 7#usize = ok (b7, closure) := by
    apply basisCallbackCross closure 7#usize 1#usize 3#usize
      alpha2Cubed alpha1 b7
      (usizeShrTwoExact 7#usize 1#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h7
  have call8 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 8#usize = ok (alpha2Squared, closure) := by
    apply basisCallbackLowZero closure 8#usize 2#usize alpha2Squared
      (usizeShrTwoExact 8#usize 2#usize rfl) (by decide) (by decide)
    rfl
  have call9 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 9#usize = ok (b9, closure) := by
    apply basisCallbackCross closure 9#usize 2#usize 1#usize
      alpha2Squared alpha1Cubed b9
      (usizeShrTwoExact 9#usize 2#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h9
  have call10 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 10#usize = ok (b10, closure) := by
    apply basisCallbackCross closure 10#usize 2#usize 2#usize
      alpha2Squared alpha1Squared b10
      (usizeShrTwoExact 10#usize 2#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h10
  have call11 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 11#usize = ok (b11, closure) := by
    apply basisCallbackCross closure 11#usize 2#usize 3#usize
      alpha2Squared alpha1 b11
      (usizeShrTwoExact 11#usize 2#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h11
  have call12 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 12#usize = ok (alpha2, closure) := by
    apply basisCallbackLowZero closure 12#usize 3#usize alpha2
      (usizeShrTwoExact 12#usize 3#usize rfl) (by decide) (by decide)
    rfl
  have call13 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 13#usize = ok (b13, closure) := by
    apply basisCallbackCross closure 13#usize 3#usize 1#usize
      alpha2 alpha1Cubed b13
      (usizeShrTwoExact 13#usize 3#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h13
  have call14 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 14#usize = ok (b14, closure) := by
    apply basisCallbackCross closure 14#usize 3#usize 2#usize
      alpha2 alpha1Squared b14
      (usizeShrTwoExact 14#usize 3#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h14
  have call15 :
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          closure 15#usize = ok (b15, closure) := by
    apply basisCallbackCross closure 15#usize 3#usize 3#usize
      alpha2 alpha1 b15
      (usizeShrTwoExact 15#usize 3#usize rfl) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) h15
  have listRun : core.array.fromFnList
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      16 0#usize closure = ok
        ([field.QM31.ONE, alpha1Cubed, alpha1Squared, alpha1,
          alpha2Cubed, b5, b6, b7, alpha2Squared, b9, b10, b11,
          alpha2, b13, b14, b15], closure) := by
    rw [core.array.fromFnList]
    simp only [call0, bind_tc_ok]
    simp only [usizeAddOneOk 0#usize 1#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call1, bind_tc_ok]
    simp only [usizeAddOneOk 1#usize 2#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call2, bind_tc_ok]
    simp only [usizeAddOneOk 2#usize 3#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call3, bind_tc_ok]
    simp only [usizeAddOneOk 3#usize 4#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call4, bind_tc_ok]
    simp only [usizeAddOneOk 4#usize 5#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call5, bind_tc_ok]
    simp only [usizeAddOneOk 5#usize 6#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call6, bind_tc_ok]
    simp only [usizeAddOneOk 6#usize 7#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call7, bind_tc_ok]
    simp only [usizeAddOneOk 7#usize 8#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call8, bind_tc_ok]
    simp only [usizeAddOneOk 8#usize 9#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call9, bind_tc_ok]
    simp only [usizeAddOneOk 9#usize 10#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call10, bind_tc_ok]
    simp only [usizeAddOneOk 10#usize 11#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call11, bind_tc_ok]
    simp only [usizeAddOneOk 11#usize 12#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call12, bind_tc_ok]
    simp only [usizeAddOneOk 12#usize 13#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call13, bind_tc_ok]
    simp only [usizeAddOneOk 13#usize 14#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call14, bind_tc_ok]
    simp only [usizeAddOneOk 14#usize 15#usize rfl, bind_tc_ok]
    rw [core.array.fromFnList]
    simp only [call15, bind_tc_ok]
  change core.array.from_fn 16#usize
      sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      closure = ok basis at run
  unfold core.array.from_fn at run
  have sixteenVal : (16#usize).val = 16 := rfl
  simp only [sixteenVal, listRun] at run
  simp at run
  exact ⟨{
    b5 := b5
    b6 := b6
    b7 := b7
    b9 := b9
    b10 := b10
    b11 := b11
    b13 := b13
    b14 := b14
    b15 := b15
    b5Run := h5
    b6Run := h6
    b7Run := h7
    b9Run := h9
    b10Run := h10
    b11Run := h11
    b13Run := h13
    b14Run := h14
    b15Run := h15
    outputExact := by
      apply Subtype.ext
      exact congrArg Subtype.val run.symm }⟩

#print axioms generated_basis_exposes_tensor_entries

end V7CallerCurrentReleaseR26GroupedRowsTwiceBasis
