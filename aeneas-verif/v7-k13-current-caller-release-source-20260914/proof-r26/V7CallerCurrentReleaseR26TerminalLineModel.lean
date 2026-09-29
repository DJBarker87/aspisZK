import V7CallerCurrentReleaseR26TerminalLineCoefficientIdentity

/-!
# Optimized terminal line result in the K1 model

The source-exact four-coefficient dot is transported to the maintained K1
field.  Deferred halving is then discharged as division by the same power of
two used by `lineBatchWeightsOne`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineModel

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26TerminalLineClaim
open V7CallerCurrentReleaseR26TerminalLineArithmetic
open V7CallerCurrentReleaseR26TerminalLineCoefficientIdentity
open V7CallerCurrentReleaseR26TerminalLineCoefficients
open AspisV5ComponentCQM31TowerExact
open AspisV5FriNaturalBasisRadix4
open AspisCircleTensorBinding

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev SourceQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def terminalLineModelDot (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Nat) (values : Array RawQM31 4#usize) : ModelQM31 :=
  ∑ index : Fin 4,
    exactRaw values.val[index.val]! *
      lineBatchWeightsOne scales xs deferred index

private theorem terminalScaleAt_eq_lineQM31At
    (scales : Slice RawQM31) (position : Nat)
    (bound : position < scales.val.length) :
    V7CallerCurrentReleaseR26TerminalLineBatch.terminalScaleAt
        scales position = lineQM31At scales position := by
  unfold V7CallerCurrentReleaseR26TerminalLineBatch.terminalScaleAt
    lineQM31At
  have left : scales.val[position] =
      @getElem! (List RawQM31) Nat RawQM31 _ _
        V7CallerCurrentReleaseR26TerminalLineBatch.instInhabitedRawQM31
        scales.val position := by
    symm
    exact @List.getElem!_of_getElem? RawQM31 scales.val[position]
      V7CallerCurrentReleaseR26TerminalLineBatch.instInhabitedRawQM31
      scales.val position (by simp [bound])
  have right : scales.val[position] =
      @getElem! (List RawQM31) Nat RawQM31 _ _
        V7CallerCurrentReleaseR26LineBatchFoldLoop.instInhabitedRawQM31
        scales.val position := by
    symm
    exact @List.getElem!_of_getElem? RawQM31 scales.val[position]
      V7CallerCurrentReleaseR26LineBatchFoldLoop.instInhabitedRawQM31
      scales.val position (by simp [bound])
  exact left.symm.trans right

private theorem terminalXAt_eq_lineM31At
    (xs : Slice RawM31) (position : Nat)
    (bound : position < xs.val.length) :
    V7CallerCurrentReleaseR26TerminalLineBatch.terminalXAt xs position =
      lineM31At xs position := by
  unfold V7CallerCurrentReleaseR26TerminalLineBatch.terminalXAt lineM31At
  have left : xs.val[position] =
      @getElem! (List RawM31) Nat RawM31 _ _
        V7CallerCurrentReleaseR26TerminalLineBatch.instInhabitedRawM31
        xs.val position := by
    symm
    exact @List.getElem!_of_getElem? RawM31 xs.val[position]
      V7CallerCurrentReleaseR26TerminalLineBatch.instInhabitedRawM31
      xs.val position (by simp [bound])
  have right : xs.val[position] =
      @getElem! (List RawM31) Nat RawM31 _ _
        V7CallerCurrentReleaseR26LineBatchFoldLoop.instInhabitedRawM31
        xs.val position := by
    symm
    exact @List.getElem!_of_getElem? RawM31 xs.val[position]
      V7CallerCurrentReleaseR26LineBatchFoldLoop.instInhabitedRawM31
      xs.val position (by simp [bound])
  exact left.symm.trans right

theorem mapped_terminal_exact_coefficient
    (scales : Slice RawQM31) (xs : Slice RawM31) (index : Fin 4)
    (scaleLength : scales.val.length = 16)
    (xLength : xs.val.length = 16) :
    sourceQm31ToModel
        (terminalExactCoefficient scales xs index.val) =
      lineBatchWeightsOne scales xs 0 index := by
  rw [terminal_exact_coefficient_natural_basis scales xs index.val index.isLt]
  change sourceQm31ToModelHom
      (∑ position ∈ Finset.range 16,
        generatedQm31ToExact
            (V7CallerCurrentReleaseR26TerminalLineBatch.terminalScaleAt
              scales position) *
          V7CallerCurrentReleaseR26QueryWeightSemantics.exactNaturalLineValue
            (generatedM31ToExact
              (V7CallerCurrentReleaseR26TerminalLineBatch.terminalXAt
                xs position)) index.val) = _
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  unfold lineBatchWeightsOne
  apply Finset.sum_congr rfl
  intro position positionMem
  simp only [map_mul, sourceQm31ToModelHom_apply]
  rw [exactNaturalLineValue_eq_model]
  have scaleBound : position.val < scales.val.length := by
    rw [scaleLength]
    exact position.isLt
  have xBound : position.val < xs.val.length := by
    rw [xLength]
    exact position.isLt
  rw [terminalScaleAt_eq_lineQM31At scales position.val scaleBound,
    terminalXAt_eq_lineM31At xs position.val xBound]
  change exactRaw
      (lineQM31At scales position) *
        naturalLineValue
          (algebraMap AspisV5ComponentCQM31TowerExact.M31Exact ModelQM31
            (generatedM31ToExact
              (lineM31At xs position))) index.val =
    lineWeightAt (lineQM31At scales position)
      (lineM31At xs position) 0 index.val
  simp only [lineWeightAt, pow_zero, div_one,
    lineQM31At, lineM31At]

theorem mapped_terminal_exact_dot
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (values : Array RawQM31 4#usize)
    (scaleLength : scales.val.length = 16)
    (xLength : xs.val.length = 16) :
    sourceQm31ToModel (terminalExactDot scales xs values) =
      terminalLineModelDot scales xs 0 values := by
  unfold terminalExactDot terminalLineModelDot
  change sourceQm31ToModelHom
      (∑ index ∈ Finset.range 4,
        terminalExactCoefficient scales xs index *
          generatedQm31ToExact values.val[index]!) = _
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro index indexMem
  simp only [map_mul, sourceQm31ToModelHom_apply]
  rw [mapped_terminal_exact_coefficient scales xs index scaleLength xLength]
  unfold exactRaw
  ring

private theorem lineBatchWeightsOne_deferred
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Nat) (index : Fin 4) :
    lineBatchWeightsOne scales xs deferred index =
      lineBatchWeightsOne scales xs 0 index /
        (2 : ModelQM31) ^ deferred := by
  unfold lineBatchWeightsOne lineWeightAt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro position positionMem
  simp

private theorem terminalLineModelDot_deferred
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Nat) (values : Array RawQM31 4#usize) :
    terminalLineModelDot scales xs deferred values =
      terminalLineModelDot scales xs 0 values /
        (2 : ModelQM31) ^ deferred := by
  unfold terminalLineModelDot
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index indexMem
  rw [lineBatchWeightsOne_deferred]
  ring

theorem terminal_line_halving_to_model
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Std.U8) (values : Array RawQM31 4#usize)
    (out : RawQM31)
    (scaleLength : scales.val.length = 16)
    (xLength : xs.val.length = 16)
    (exact : (2 : SourceQM31) ^ deferred.val *
        generatedQm31ToExact out = terminalExactDot scales xs values) :
    sourceQm31ToModel (generatedQm31ToExact out) =
      terminalLineModelDot scales xs deferred.val values := by
  have mapped := congrArg sourceQm31ToModel exact
  have mappedPower : sourceQm31ToModel
      ((2 : SourceQM31) ^ deferred.val) =
        (2 : ModelQM31) ^ deferred.val := by
    change sourceQm31ToModelHom ((2 : SourceQM31) ^ deferred.val) = _
    rw [map_pow, map_ofNat]
  rw [sourceQm31ToModel_mul, mappedPower,
    mapped_terminal_exact_dot scales xs values scaleLength xLength] at mapped
  rw [terminalLineModelDot_deferred]
  have twoNonzero : (2 : ModelQM31) ≠ 0 := by decide
  field_simp [twoNonzero]
  simpa [mul_comm] using mapped

#print axioms mapped_terminal_exact_coefficient
#print axioms mapped_terminal_exact_dot
#print axioms terminal_line_halving_to_model

end V7CallerCurrentReleaseR26TerminalLineModel
