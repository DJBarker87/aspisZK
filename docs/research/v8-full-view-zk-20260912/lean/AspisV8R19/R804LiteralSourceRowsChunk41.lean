import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk21
import AspisV8R19.R799ActiveSourceCellsChunk22
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk41
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk41
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow918 (j : Fin 222) : M := if j.val = 164 then 2147483612 else if j.val = 165 then 2147483409 else 0

theorem literalSourceMatrix_row918 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨165, by decide⟩ : Fin 214)) = literalRow918 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 164
  · have hj : j = (⟨164, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow918]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 918 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s0_row918_col164
  by_cases h1 : j.val = 165
  · have hj : j = (⟨165, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow918, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 918 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s1_row918_col165
  · simp [literalRow918, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk41.row918_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row918

def literalRow920 (j : Fin 222) : M := if j.val = 164 then 536870913 else if j.val = 165 then 536870913 else if j.val = 166 then 1073741772 else if j.val = 167 then 1073741483 else if j.val = 168 then 536870913 else if j.val = 169 then 536870913 else 0

theorem literalSourceMatrix_row920 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨166, by decide⟩ : Fin 214)) = literalRow920 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 164
  · have hj : j = (⟨164, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow920]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s0_row920_col164
  by_cases h1 : j.val = 165
  · have hj : j = (⟨165, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow920, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d229_s1_row920_col165
  by_cases h2 : j.val = 166
  · have hj : j = (⟨166, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow920, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk21.cell_d230_s0_row920_col166
  by_cases h3 : j.val = 167
  · have hj : j = (⟨167, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow920, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d230_s1_row920_col167
  by_cases h4 : j.val = 168
  · have hj : j = (⟨168, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow920, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s0_row920_col168
  by_cases h5 : j.val = 169
  · have hj : j = (⟨169, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow920, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s1_row920_col169
  · simp [literalRow920, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk41.row920_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row920

def literalRow922 (j : Fin 222) : M := if j.val = 166 then 2147483612 else if j.val = 167 then 2147483409 else 0

theorem literalSourceMatrix_row922 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨167, by decide⟩ : Fin 214)) = literalRow922 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 166
  · have hj : j = (⟨166, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow922]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 922 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d230_s0_row922_col166
  by_cases h1 : j.val = 167
  · have hj : j = (⟨167, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow922, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 922 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d230_s1_row922_col167
  · simp [literalRow922, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk41.row922_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row922

def literalRow924 (j : Fin 222) : M := if j.val = 166 then 1073741826 else if j.val = 167 then 1073741826 else if j.val = 168 then 1073741772 else if j.val = 169 then 1073741483 else 0

theorem literalSourceMatrix_row924 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨168, by decide⟩ : Fin 214)) = literalRow924 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 166
  · have hj : j = (⟨166, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow924]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 924 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d230_s0_row924_col166
  by_cases h1 : j.val = 167
  · have hj : j = (⟨167, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow924, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 924 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d230_s1_row924_col167
  by_cases h2 : j.val = 168
  · have hj : j = (⟨168, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow924, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 924 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s0_row924_col168
  by_cases h3 : j.val = 169
  · have hj : j = (⟨169, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow924, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 924 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s1_row924_col169
  · simp [literalRow924, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk41.row924_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row924

end
end AspisV8R19.R804LiteralSourceRowsChunk41
