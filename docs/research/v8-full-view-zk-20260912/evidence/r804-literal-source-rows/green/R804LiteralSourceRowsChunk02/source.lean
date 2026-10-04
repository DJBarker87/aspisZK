import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk01
import AspisV8R19.R797ActiveSourceCellsChunk02
import AspisV8R19.R799ActiveSourceCellsChunk00
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk02
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk02
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow132 (j : Fin 222) : M := if j.val = 7 then 1073741826 else if j.val = 8 then 1073741826 else if j.val = 9 then 1073741772 else if j.val = 10 then 1073741483 else 0

theorem literalSourceMatrix_row132 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨9, by decide⟩ : Fin 214)) = literalRow132 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 7
  · have hj : j = (⟨7, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow132]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d32_s0_row132_col7
  by_cases h1 : j.val = 8
  · have hj : j = (⟨8, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow132, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d32_s1_row132_col8
  by_cases h2 : j.val = 9
  · have hj : j = (⟨9, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow132, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s0_row132_col9
  by_cases h3 : j.val = 10
  · have hj : j = (⟨10, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow132, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s1_row132_col10
  · simp [literalRow132, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk02.row132_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row132

def literalRow134 (j : Fin 222) : M := if j.val = 9 then 2147483612 else if j.val = 10 then 2147483409 else 0

theorem literalSourceMatrix_row134 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨10, by decide⟩ : Fin 214)) = literalRow134 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 9
  · have hj : j = (⟨9, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow134]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 134 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s0_row134_col9
  by_cases h1 : j.val = 10
  · have hj : j = (⟨10, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow134, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 134 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s1_row134_col10
  · simp [literalRow134, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk02.row134_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row134

def literalRow136 (j : Fin 222) : M := if j.val = 9 then 536870913 else if j.val = 10 then 536870913 else if j.val = 11 then 1073741772 else if j.val = 12 then 1073741483 else if j.val = 13 then 536870913 else if j.val = 14 then 536870913 else 0

theorem literalSourceMatrix_row136 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨11, by decide⟩ : Fin 214)) = literalRow136 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 9
  · have hj : j = (⟨9, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow136]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s0_row136_col9
  by_cases h1 : j.val = 10
  · have hj : j = (⟨10, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow136, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d33_s1_row136_col10
  by_cases h2 : j.val = 11
  · have hj : j = (⟨11, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow136, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨34, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d34_s0_row136_col11
  by_cases h3 : j.val = 12
  · have hj : j = (⟨12, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow136, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨34, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d34_s1_row136_col12
  by_cases h4 : j.val = 13
  · have hj : j = (⟨13, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow136, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s0_row136_col13
  by_cases h5 : j.val = 14
  · have hj : j = (⟨14, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow136, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s1_row136_col14
  · simp [literalRow136, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk02.row136_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row136

def literalRow138 (j : Fin 222) : M := if j.val = 11 then 2147483612 else if j.val = 12 then 2147483409 else 0

theorem literalSourceMatrix_row138 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨12, by decide⟩ : Fin 214)) = literalRow138 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 11
  · have hj : j = (⟨11, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow138]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨34, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 138 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d34_s0_row138_col11
  by_cases h1 : j.val = 12
  · have hj : j = (⟨12, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow138, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨34, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 138 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d34_s1_row138_col12
  · simp [literalRow138, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk02.row138_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row138

end
end AspisV8R19.R804LiteralSourceRowsChunk02
