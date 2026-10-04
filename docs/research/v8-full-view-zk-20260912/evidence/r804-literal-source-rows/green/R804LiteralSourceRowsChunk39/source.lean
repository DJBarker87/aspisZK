import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk19
import AspisV8R19.R799ActiveSourceCellsChunk20
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk39
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk39
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow902 (j : Fin 222) : M := if j.val = 156 then 2147483612 else if j.val = 157 then 2147483409 else 0

theorem literalSourceMatrix_row902 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨157, by decide⟩ : Fin 214)) = literalRow902 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 156
  · have hj : j = (⟨156, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow902]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨225, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 902 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d225_s0_row902_col156
  by_cases h1 : j.val = 157
  · have hj : j = (⟨157, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow902, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨225, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 902 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d225_s1_row902_col157
  · simp [literalRow902, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk39.row902_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row902

def literalRow904 (j : Fin 222) : M := if j.val = 156 then 536870913 else if j.val = 157 then 536870913 else if j.val = 158 then 1073741772 else if j.val = 159 then 1073741483 else if j.val = 160 then 536870913 else if j.val = 161 then 536870913 else 0

theorem literalSourceMatrix_row904 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨158, by decide⟩ : Fin 214)) = literalRow904 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 156
  · have hj : j = (⟨156, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow904]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨225, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 904 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d225_s0_row904_col156
  by_cases h1 : j.val = 157
  · have hj : j = (⟨157, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow904, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨225, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 904 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d225_s1_row904_col157
  by_cases h2 : j.val = 158
  · have hj : j = (⟨158, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow904, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨226, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 904 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d226_s0_row904_col158
  by_cases h3 : j.val = 159
  · have hj : j = (⟨159, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow904, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨226, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 904 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d226_s1_row904_col159
  by_cases h4 : j.val = 160
  · have hj : j = (⟨160, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow904, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 904 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s0_row904_col160
  by_cases h5 : j.val = 161
  · have hj : j = (⟨161, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow904, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 904 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s1_row904_col161
  · simp [literalRow904, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk39.row904_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row904

def literalRow906 (j : Fin 222) : M := if j.val = 158 then 2147483612 else if j.val = 159 then 2147483409 else 0

theorem literalSourceMatrix_row906 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨159, by decide⟩ : Fin 214)) = literalRow906 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 158
  · have hj : j = (⟨158, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow906]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨226, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 906 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d226_s0_row906_col158
  by_cases h1 : j.val = 159
  · have hj : j = (⟨159, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow906, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨226, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 906 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d226_s1_row906_col159
  · simp [literalRow906, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk39.row906_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row906

def literalRow908 (j : Fin 222) : M := if j.val = 158 then 1073741826 else if j.val = 159 then 1073741826 else if j.val = 160 then 1073741772 else if j.val = 161 then 1073741483 else 0

theorem literalSourceMatrix_row908 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨160, by decide⟩ : Fin 214)) = literalRow908 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 158
  · have hj : j = (⟨158, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow908]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨226, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 908 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d226_s0_row908_col158
  by_cases h1 : j.val = 159
  · have hj : j = (⟨159, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow908, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨226, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 908 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d226_s1_row908_col159
  by_cases h2 : j.val = 160
  · have hj : j = (⟨160, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow908, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 908 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s0_row908_col160
  by_cases h3 : j.val = 161
  · have hj : j = (⟨161, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow908, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 908 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s1_row908_col161
  · simp [literalRow908, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk39.row908_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row908

end
end AspisV8R19.R804LiteralSourceRowsChunk39
