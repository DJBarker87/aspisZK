import PoseidonExternalColumnSumsV4
import AspisR1.PoseidonGroupSliceModel
import PoseidonExternalColumn1Reassembly
import RawPoseidonRowField
import PoseidonExternalColumnCallV21
import PoseidonExternalColumnArrayCallV3
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalColumnSumField
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonGroupSliceModel
open AspisR1.PoseidonExternalColumn1Reassembly
open AspisR1.RawPoseidonRowField

abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31
abbrev Sums := Array (Array Std.U64 4#usize) 4#usize
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

def rowWordsAt (state : State) (row column : Fin 4) : Fin 4 → Nat :=
  qWords (cell16 state row column)

def fieldColumnSum (state : State) (column : Fin 4) : Exact :=
  ((decodeWords (rowWordsAt state 0 column) +
      decodeWords (rowWordsAt state 1 column)) +
      decodeWords (rowWordsAt state 2 column)) +
      decodeWords (rowWordsAt state 3 column)

private theorem limb_words (q : QM) (j : Fin 4) :
    (AspisR1.PoseidonExternalColumnCall.limbAt q
      (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt).val = qWords q j := by
  fin_cases j <;> simp [AspisR1.PoseidonExternalColumnCall.limbAt,
    AspisR1.PoseidonExternalColumnCall.limbs32, qWords, Array.make]

private theorem state_column_rows (state : State) (column : Fin 4) :
    state.val[(UScalar.ofNatCore column.val (by scalar_tac) : Usize).val]'(by have := column.isLt; scalar_tac) = cell16 state 0 column ∧
    state.val[4+(UScalar.ofNatCore column.val (by scalar_tac) : Usize).val]'(by have := column.isLt; scalar_tac) = cell16 state 1 column ∧
    state.val[8+(UScalar.ofNatCore column.val (by scalar_tac) : Usize).val]'(by have := column.isLt; scalar_tac) = cell16 state 2 column ∧
    state.val[12+(UScalar.ofNatCore column.val (by scalar_tac) : Usize).val]'(by have := column.isLt; scalar_tac) = cell16 state 3 column := by
  constructor
  · simp [cell16]
  constructor
  · simp [cell16]
  constructor
  · simp [cell16]
  · simp [cell16]

theorem source_column_decode (state : State) (sums : Sums)
    (hcolumns : ∀ i j : Fin 4,
      AspisR1.PoseidonExternalColumnArrayCall.columnTotal state
        (UScalar.ofNatCore i.val (by scalar_tac)) (by scalar_tac) j
        (AspisR1.PoseidonExternalColumnSums.sumWordAt sums i j))
    (column : Fin 4) :
    decodeWords (sumWords sums column) = fieldColumnSum state column := by
  have ⟨hr0,hr1,hr2,hr3⟩ := state_column_rows state column
  have hwords : sumWords sums column = fun j =>
      rowWordsAt state 0 column j + rowWordsAt state 1 column j +
      rowWordsAt state 2 column j + rowWordsAt state 3 column j := by
    funext j
    have hc := hcolumns column j
    have hj0 := limb_words (cell16 state 0 column) j
    have hj1 := limb_words (cell16 state 1 column) j
    have hj2 := limb_words (cell16 state 2 column) j
    have hj3 := limb_words (cell16 state 3 column) j
    dsimp [AspisR1.PoseidonExternalColumnArrayCall.columnTotal,
      AspisR1.PoseidonExternalColumnCall.sumFour] at hc
    rw [hr0,hr1,hr2,hr3,hj0,hj1,hj2,hj3] at hc
    change sumWords sums column j = _
    simpa [sumWords, AspisR1.PoseidonExternalColumnSums.sumWordAt,
      AspisR1.PoseidonFullRoundCellStep.cell, rowWordsAt] using hc
  rw [hwords]
  simp only [decodeWords_add, fieldColumnSum]

#print axioms source_column_decode
end AspisR1.PoseidonExternalColumnSumField
