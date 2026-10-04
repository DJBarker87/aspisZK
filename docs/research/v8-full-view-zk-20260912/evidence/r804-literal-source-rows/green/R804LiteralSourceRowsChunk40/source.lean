import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk20
import AspisV8R19.R799ActiveSourceCellsChunk21
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk40
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk40
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow910 (j : Fin 222) : M := if j.val = 160 then 2147483612 else if j.val = 161 then 2147483409 else 0

theorem literalSourceMatrix_row910 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨161, by decide⟩ : Fin 214)) = literalRow910 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 160
  · have hj : j = (⟨160, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow910]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 910 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s0_row910_col160
  by_cases h1 : j.val = 161
  · have hj : j = (⟨161, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow910, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 910 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s1_row910_col161
  · simp [literalRow910, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk40.row910_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row910

def literalRow912 (j : Fin 222) : M := if j.val = 160 then 1342177280 else if j.val = 161 then 1342177280 else if j.val = 162 then 1073741772 else if j.val = 163 then 1073741483 else if j.val = 164 then 536870913 else if j.val = 165 then 536870913 else if j.val = 168 then 1342177280 else if j.val = 169 then 1342177280 else 0

theorem literalSourceMatrix_row912 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨162, by decide⟩ : Fin 214)) = literalRow912 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 160
  · have hj : j = (⟨160, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow912]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s0_row912_col160
  by_cases h1 : j.val = 161
  · have hj : j = (⟨161, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow912, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨227, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d227_s1_row912_col161
  by_cases h2 : j.val = 162
  · have hj : j = (⟨162, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow912, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk20.cell_d228_s0_row912_col162
  by_cases h3 : j.val = 163
  · have hj : j = (⟨163, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow912, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d228_s1_row912_col163
  by_cases h4 : j.val = 164
  · have hj : j = (⟨164, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow912, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s0_row912_col164
  by_cases h5 : j.val = 165
  · have hj : j = (⟨165, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow912, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s1_row912_col165
  by_cases h6 : j.val = 168
  · have hj : j = (⟨168, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow912, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d231_s0_row912_col168
  by_cases h7 : j.val = 169
  · have hj : j = (⟨169, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow912, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d231_s1_row912_col169
  · simp [literalRow912, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk40.row912_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
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
#print axioms literalSourceMatrix_row912

def literalRow914 (j : Fin 222) : M := if j.val = 162 then 2147483612 else if j.val = 163 then 2147483409 else 0

theorem literalSourceMatrix_row914 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨163, by decide⟩ : Fin 214)) = literalRow914 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 162
  · have hj : j = (⟨162, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow914]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 914 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d228_s0_row914_col162
  by_cases h1 : j.val = 163
  · have hj : j = (⟨163, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow914, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 914 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d228_s1_row914_col163
  · simp [literalRow914, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk40.row914_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row914

def literalRow916 (j : Fin 222) : M := if j.val = 162 then 1073741826 else if j.val = 163 then 1073741826 else if j.val = 164 then 1073741772 else if j.val = 165 then 1073741483 else 0

theorem literalSourceMatrix_row916 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨164, by decide⟩ : Fin 214)) = literalRow916 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 162
  · have hj : j = (⟨162, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow916]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d228_s0_row916_col162
  by_cases h1 : j.val = 163
  · have hj : j = (⟨163, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow916, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d228_s1_row916_col163
  by_cases h2 : j.val = 164
  · have hj : j = (⟨164, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow916, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s0_row916_col164
  by_cases h3 : j.val = 165
  · have hj : j = (⟨165, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow916, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s1_row916_col165
  · simp [literalRow916, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk40.row916_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row916

end
end AspisV8R19.R804LiteralSourceRowsChunk40
