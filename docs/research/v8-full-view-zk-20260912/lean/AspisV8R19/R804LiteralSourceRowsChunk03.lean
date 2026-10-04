import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk02
import AspisV8R19.R797ActiveSourceCellsChunk03
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk03
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk03
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow140 (j : Fin 222) : M := if j.val = 11 then 1073741826 else if j.val = 12 then 1073741826 else if j.val = 13 then 1073741772 else if j.val = 14 then 1073741483 else 0

theorem literalSourceMatrix_row140 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨13, by decide⟩ : Fin 214)) = literalRow140 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 11
  · have hj : j = (⟨11, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow140]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨34, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 140 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d34_s0_row140_col11
  by_cases h1 : j.val = 12
  · have hj : j = (⟨12, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow140, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨34, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 140 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d34_s1_row140_col12
  by_cases h2 : j.val = 13
  · have hj : j = (⟨13, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow140, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 140 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s0_row140_col13
  by_cases h3 : j.val = 14
  · have hj : j = (⟨14, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow140, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 140 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s1_row140_col14
  · simp [literalRow140, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk03.row140_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row140

def literalRow142 (j : Fin 222) : M := if j.val = 13 then 2147483612 else if j.val = 14 then 2147483409 else 0

theorem literalSourceMatrix_row142 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨14, by decide⟩ : Fin 214)) = literalRow142 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 13
  · have hj : j = (⟨13, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow142]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 142 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s0_row142_col13
  by_cases h1 : j.val = 14
  · have hj : j = (⟨14, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow142, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 142 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s1_row142_col14
  · simp [literalRow142, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk03.row142_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row142

def literalRow144 (j : Fin 222) : M := if j.val = 13 then 1342177280 else if j.val = 14 then 1342177280 else if j.val = 15 then 1073741772 else if j.val = 16 then 1073741483 else if j.val = 17 then 536870913 else if j.val = 18 then 536870913 else if j.val = 21 then 1342177280 else if j.val = 22 then 1342177280 else 0

theorem literalSourceMatrix_row144 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨15, by decide⟩ : Fin 214)) = literalRow144 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 13
  · have hj : j = (⟨13, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow144]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s0_row144_col13
  by_cases h1 : j.val = 14
  · have hj : j = (⟨14, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow144, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d35_s1_row144_col14
  by_cases h2 : j.val = 15
  · have hj : j = (⟨15, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow144, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨36, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk02.cell_d36_s0_row144_col15
  by_cases h3 : j.val = 16
  · have hj : j = (⟨16, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow144, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨36, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d36_s1_row144_col16
  by_cases h4 : j.val = 17
  · have hj : j = (⟨17, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow144, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s0_row144_col17
  by_cases h5 : j.val = 18
  · have hj : j = (⟨18, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow144, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s1_row144_col18
  by_cases h6 : j.val = 21
  · have hj : j = (⟨21, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow144, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d39_s0_row144_col21
  by_cases h7 : j.val = 22
  · have hj : j = (⟨22, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow144, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 144 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d39_s1_row144_col22
  · simp [literalRow144, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk03.row144_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
    · exact h7 hbad
#print axioms literalSourceMatrix_row144

def literalRow146 (j : Fin 222) : M := if j.val = 15 then 2147483612 else if j.val = 16 then 2147483409 else 0

theorem literalSourceMatrix_row146 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨16, by decide⟩ : Fin 214)) = literalRow146 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 15
  · have hj : j = (⟨15, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow146]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨36, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 146 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d36_s0_row146_col15
  by_cases h1 : j.val = 16
  · have hj : j = (⟨16, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow146, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨36, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 146 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d36_s1_row146_col16
  · simp [literalRow146, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk03.row146_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row146

end
end AspisV8R19.R804LiteralSourceRowsChunk03
