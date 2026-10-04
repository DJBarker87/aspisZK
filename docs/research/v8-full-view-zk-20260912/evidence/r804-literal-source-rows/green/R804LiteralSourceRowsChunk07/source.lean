import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk05
import AspisV8R19.R797ActiveSourceCellsChunk06
import AspisV8R19.R799ActiveSourceCellsChunk01
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk07
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk07
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow172 (j : Fin 222) : M := if j.val = 27 then 1073741826 else if j.val = 28 then 1073741826 else if j.val = 29 then 1073741772 else if j.val = 30 then 1073741483 else 0

theorem literalSourceMatrix_row172 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨29, by decide⟩ : Fin 214)) = literalRow172 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 27
  · have hj : j = (⟨27, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow172]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨42, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 172 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d42_s0_row172_col27
  by_cases h1 : j.val = 28
  · have hj : j = (⟨28, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow172, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨42, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 172 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d42_s1_row172_col28
  by_cases h2 : j.val = 29
  · have hj : j = (⟨29, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow172, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 172 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d43_s0_row172_col29
  by_cases h3 : j.val = 30
  · have hj : j = (⟨30, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow172, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 172 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d43_s1_row172_col30
  · simp [literalRow172, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk07.row172_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row172

def literalRow174 (j : Fin 222) : M := if j.val = 29 then 2147483612 else if j.val = 30 then 2147483409 else 0

theorem literalSourceMatrix_row174 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨30, by decide⟩ : Fin 214)) = literalRow174 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 29
  · have hj : j = (⟨29, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow174]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 174 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d43_s0_row174_col29
  by_cases h1 : j.val = 30
  · have hj : j = (⟨30, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow174, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 174 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d43_s1_row174_col30
  · simp [literalRow174, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk07.row174_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row174

def literalRow176 (j : Fin 222) : M := if j.val = 29 then 1342177280 else if j.val = 30 then 1342177280 else if j.val = 31 then 1073741772 else if j.val = 32 then 1073741483 else if j.val = 33 then 536870913 else if j.val = 35 then 1342177280 else 0

theorem literalSourceMatrix_row176 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨31, by decide⟩ : Fin 214)) = literalRow176 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 29
  · have hj : j = (⟨29, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow176]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d43_s0_row176_col29
  by_cases h1 : j.val = 30
  · have hj : j = (⟨30, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow176, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d43_s1_row176_col30
  by_cases h2 : j.val = 31
  · have hj : j = (⟨31, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow176, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d44_s0_row176_col31
  by_cases h3 : j.val = 32
  · have hj : j = (⟨32, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow176, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d44_s1_row176_col32
  by_cases h4 : j.val = 33
  · have hj : j = (⟨33, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow176, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d45_s0_row176_col33
  by_cases h5 : j.val = 35
  · have hj : j = (⟨35, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow176, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d47_s1_row176_col35
  · simp [literalRow176, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk07.row176_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row176

def literalRow178 (j : Fin 222) : M := if j.val = 31 then 2147483612 else if j.val = 32 then 2147483409 else if j.val = 221 then 1342177280 else 0

theorem literalSourceMatrix_row178 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨32, by decide⟩ : Fin 214)) = literalRow178 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 31
  · have hj : j = (⟨31, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow178]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 178 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d44_s0_row178_col31
  by_cases h1 : j.val = 32
  · have hj : j = (⟨32, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow178, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 178 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d44_s1_row178_col32
  by_cases h2 : j.val = 221
  · have hj : j = (⟨221, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow178, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 178 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d47_s2_row178_col221
  · simp [literalRow178, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk07.row178_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row178

end
end AspisV8R19.R804LiteralSourceRowsChunk07
