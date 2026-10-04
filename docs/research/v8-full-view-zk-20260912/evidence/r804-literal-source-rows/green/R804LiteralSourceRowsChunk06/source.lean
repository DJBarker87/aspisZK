import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk05
import AspisV8R19.R799ActiveSourceCellsChunk00
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk06
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk06
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow164 (j : Fin 222) : M := if j.val = 23 then 1073741826 else if j.val = 24 then 1073741826 else if j.val = 25 then 1073741772 else if j.val = 26 then 1073741483 else 0

theorem literalSourceMatrix_row164 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨25, by decide⟩ : Fin 214)) = literalRow164 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 23
  · have hj : j = (⟨23, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow164]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 164 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d40_s0_row164_col23
  by_cases h1 : j.val = 24
  · have hj : j = (⟨24, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow164, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 164 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d40_s1_row164_col24
  by_cases h2 : j.val = 25
  · have hj : j = (⟨25, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow164, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 164 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d41_s0_row164_col25
  by_cases h3 : j.val = 26
  · have hj : j = (⟨26, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow164, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 164 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d41_s1_row164_col26
  · simp [literalRow164, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk06.row164_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row164

def literalRow166 (j : Fin 222) : M := if j.val = 25 then 2147483612 else if j.val = 26 then 2147483409 else 0

theorem literalSourceMatrix_row166 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨26, by decide⟩ : Fin 214)) = literalRow166 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 25
  · have hj : j = (⟨25, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow166]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 166 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d41_s0_row166_col25
  by_cases h1 : j.val = 26
  · have hj : j = (⟨26, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow166, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 166 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d41_s1_row166_col26
  · simp [literalRow166, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk06.row166_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row166

def literalRow168 (j : Fin 222) : M := if j.val = 25 then 536870913 else if j.val = 26 then 536870913 else if j.val = 27 then 1073741772 else if j.val = 28 then 1073741483 else if j.val = 29 then 536870913 else if j.val = 30 then 536870913 else 0

theorem literalSourceMatrix_row168 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨27, by decide⟩ : Fin 214)) = literalRow168 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 25
  · have hj : j = (⟨25, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow168]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 168 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d41_s0_row168_col25
  by_cases h1 : j.val = 26
  · have hj : j = (⟨26, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow168, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 168 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d41_s1_row168_col26
  by_cases h2 : j.val = 27
  · have hj : j = (⟨27, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow168, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨42, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 168 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d42_s0_row168_col27
  by_cases h3 : j.val = 28
  · have hj : j = (⟨28, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow168, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨42, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 168 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d42_s1_row168_col28
  by_cases h4 : j.val = 29
  · have hj : j = (⟨29, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow168, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 168 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d43_s0_row168_col29
  by_cases h5 : j.val = 30
  · have hj : j = (⟨30, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow168, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 168 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d43_s1_row168_col30
  · simp [literalRow168, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk06.row168_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row168

def literalRow170 (j : Fin 222) : M := if j.val = 27 then 2147483612 else if j.val = 28 then 2147483409 else 0

theorem literalSourceMatrix_row170 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨28, by decide⟩ : Fin 214)) = literalRow170 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 27
  · have hj : j = (⟨27, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow170]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨42, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 170 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d42_s0_row170_col27
  by_cases h1 : j.val = 28
  · have hj : j = (⟨28, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow170, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨42, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 170 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d42_s1_row170_col28
  · simp [literalRow170, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk06.row170_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row170

end
end AspisV8R19.R804LiteralSourceRowsChunk06
