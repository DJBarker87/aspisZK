import AspisR1.CopyPatternRegistryModelA
import AspisR1.CopyPatternRegistryModelB

/-! The fixed source pattern registry has the same fourteen model descriptors. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternRegistryModel
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact

theorem raw_columns (index : Fin 14) : ∀ j : Fin 16,
    (cell (rawAt index).columns j).val < 16 := by
  fin_cases index
  · exact raw0_columns
  · exact raw1_columns
  · exact raw2_columns
  · exact raw3_columns
  · exact raw4_columns
  · exact raw5_columns
  · exact raw6_columns
  · exact raw7_columns
  · exact raw8_columns
  · exact raw9_columns
  · exact raw10_columns
  · exact raw11_columns
  · exact raw12_columns
  · exact raw13_columns

theorem raw_offsets (index : Fin 14) : ∀ j : Fin 16,
    (cell (rawAt index).offsets j).val < AspisR1.TerminalLiftM31Exact.P := by
  fin_cases index
  · exact raw0_offsets
  · exact raw1_offsets
  · exact raw2_offsets
  · exact raw3_offsets
  · exact raw4_offsets
  · exact raw5_offsets
  · exact raw6_offsets
  · exact raw7_offsets
  · exact raw8_offsets
  · exact raw9_offsets
  · exact raw10_offsets
  · exact raw11_offsets
  · exact raw12_offsets
  · exact raw13_offsets

theorem raw_model (index : Fin 14) :
    modelPattern (rawAt index) (raw_columns index) = R0P.copyPatterns index := by
  fin_cases index
  · change modelPattern (rawAt 0) (raw_columns 0) = R0P.copyPattern0
    exact raw0_model
  · change modelPattern (rawAt 1) (raw_columns 1) = R0P.copyPattern1
    exact raw1_model
  · change modelPattern (rawAt 2) (raw_columns 2) = R0P.copyPattern2
    exact raw2_model
  · change modelPattern (rawAt 3) (raw_columns 3) = R0P.copyPattern3
    exact raw3_model
  · change modelPattern (rawAt 4) (raw_columns 4) = R0P.copyPattern4
    exact raw4_model
  · change modelPattern (rawAt 5) (raw_columns 5) = R0P.copyPattern5
    exact raw5_model
  · change modelPattern (rawAt 6) (raw_columns 6) = R0P.copyPattern6
    exact raw6_model
  · change modelPattern (rawAt 7) (raw_columns 7) = R0P.copyPattern7
    exact raw7_model
  · change modelPattern (rawAt 8) (raw_columns 8) = R0P.copyPattern8
    exact raw8_model
  · change modelPattern (rawAt 9) (raw_columns 9) = R0P.copyPattern9
    exact raw9_model
  · change modelPattern (rawAt 10) (raw_columns 10) = R0P.copyPattern10
    exact raw10_model
  · change modelPattern (rawAt 11) (raw_columns 11) = R0P.copyPattern11
    exact raw11_model
  · change modelPattern (rawAt 12) (raw_columns 12) = R0P.copyPattern12
    exact raw12_model
  · change modelPattern (rawAt 13) (raw_columns 13) = R0P.copyPattern13
    exact raw13_model

theorem registry_read (index : Usize) (hindex : index.val < 14) :
    Array.index_usize Registry index = .ok (rawAt ⟨index.val,hindex⟩) := by
  exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok Registry index hindex

#print axioms raw_columns
#print axioms raw_offsets
#print axioms raw_model
#print axioms registry_read
end
end AspisR1.CopyPatternRegistryModel
