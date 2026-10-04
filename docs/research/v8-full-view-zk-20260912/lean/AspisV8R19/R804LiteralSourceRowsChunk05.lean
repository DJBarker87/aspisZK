import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk04
import AspisV8R19.R797ActiveSourceCellsChunk05
import AspisV8R19.R799ActiveSourceCellsChunk00
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk05
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk05
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow156 (j : Fin 222) : M := if j.val = 19 then 1073741826 else if j.val = 20 then 1073741826 else if j.val = 21 then 1073741772 else if j.val = 22 then 1073741483 else 0

theorem literalSourceMatrix_row156 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨21, by decide⟩ : Fin 214)) = literalRow156 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 19
  · have hj : j = (⟨19, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow156]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨38, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 156 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d38_s0_row156_col19
  by_cases h1 : j.val = 20
  · have hj : j = (⟨20, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow156, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨38, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 156 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d38_s1_row156_col20
  by_cases h2 : j.val = 21
  · have hj : j = (⟨21, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow156, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 156 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s0_row156_col21
  by_cases h3 : j.val = 22
  · have hj : j = (⟨22, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow156, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 156 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s1_row156_col22
  · simp [literalRow156, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk05.row156_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row156

def literalRow158 (j : Fin 222) : M := if j.val = 21 then 2147483612 else if j.val = 22 then 2147483409 else 0

theorem literalSourceMatrix_row158 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨22, by decide⟩ : Fin 214)) = literalRow158 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 21
  · have hj : j = (⟨21, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow158]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 158 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s0_row158_col21
  by_cases h1 : j.val = 22
  · have hj : j = (⟨22, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow158, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 158 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s1_row158_col22
  · simp [literalRow158, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk05.row158_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row158

def literalRow160 (j : Fin 222) : M := if j.val = 21 then 671088640 else if j.val = 22 then 671088640 else if j.val = 23 then 1073741772 else if j.val = 24 then 1073741483 else if j.val = 25 then 536870913 else if j.val = 26 then 536870913 else if j.val = 29 then 1342177280 else if j.val = 30 then 1342177280 else if j.val = 35 then 671088640 else 0

theorem literalSourceMatrix_row160 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨23, by decide⟩ : Fin 214)) = literalRow160 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 21
  · have hj : j = (⟨21, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow160]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s0_row160_col21
  by_cases h1 : j.val = 22
  · have hj : j = (⟨22, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow160, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s1_row160_col22
  by_cases h2 : j.val = 23
  · have hj : j = (⟨23, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow160, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d40_s0_row160_col23
  by_cases h3 : j.val = 24
  · have hj : j = (⟨24, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow160, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d40_s1_row160_col24
  by_cases h4 : j.val = 25
  · have hj : j = (⟨25, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow160, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d41_s0_row160_col25
  by_cases h5 : j.val = 26
  · have hj : j = (⟨26, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow160, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨41, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d41_s1_row160_col26
  by_cases h6 : j.val = 29
  · have hj : j = (⟨29, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow160, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d43_s0_row160_col29
  by_cases h7 : j.val = 30
  · have hj : j = (⟨30, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow160, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk05.cell_d43_s1_row160_col30
  by_cases h8 : j.val = 35
  · have hj : j = (⟨35, by decide⟩ : Fin 222) := Fin.ext h8
    subst j
    simp [literalRow160, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d47_s1_row160_col35
  · simp [literalRow160, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk05.row160_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
    · exact h7 hbad
    · exact h8 hbad
#print axioms literalSourceMatrix_row160

def literalRow162 (j : Fin 222) : M := if j.val = 23 then 2147483612 else if j.val = 24 then 2147483409 else if j.val = 221 then 671088640 else 0

theorem literalSourceMatrix_row162 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨24, by decide⟩ : Fin 214)) = literalRow162 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 23
  · have hj : j = (⟨23, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow162]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 162 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d40_s0_row162_col23
  by_cases h1 : j.val = 24
  · have hj : j = (⟨24, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow162, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 162 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d40_s1_row162_col24
  by_cases h2 : j.val = 221
  · have hj : j = (⟨221, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow162, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 162 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d47_s2_row162_col221
  · simp [literalRow162, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk05.row162_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row162

end
end AspisV8R19.R804LiteralSourceRowsChunk05
