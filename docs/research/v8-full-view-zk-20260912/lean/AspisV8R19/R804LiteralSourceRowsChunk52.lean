import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk31
import AspisV8R19.R799ActiveSourceCellsChunk32
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk52
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk52
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow1013 (j : Fin 222) : M := if j.val = 208 then 1073741826 else if j.val = 209 then 42 else if j.val = 210 then 1073743541 else 0

theorem literalSourceMatrix_row1013 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨209, by decide⟩ : Fin 214)) = literalRow1013 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 208
  · have hj : j = (⟨208, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1013]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1013 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d252_s2_row1013_col208
  by_cases h1 : j.val = 209
  · have hj : j = (⟨209, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1013, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1013 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d253_s0_row1013_col209
  by_cases h2 : j.val = 210
  · have hj : j = (⟨210, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow1013, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1013 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d253_s2_row1013_col210
  · simp [literalRow1013, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk52.row1013_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row1013

def literalRow1015 (j : Fin 222) : M := if j.val = 209 then 5 else if j.val = 210 then 7 else 0

theorem literalSourceMatrix_row1015 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨210, by decide⟩ : Fin 214)) = literalRow1015 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 209
  · have hj : j = (⟨209, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1015]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1015 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d253_s0_row1015_col209
  by_cases h1 : j.val = 210
  · have hj : j = (⟨210, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1015, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1015 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d253_s2_row1015_col210
  · simp [literalRow1015, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk52.row1015_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row1015

def literalRow1017 (j : Fin 222) : M := if j.val = 210 then 536870913 else if j.val = 211 then 42 else if j.val = 212 then 1073743541 else if j.val = 213 then 245 else 0

theorem literalSourceMatrix_row1017 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨211, by decide⟩ : Fin 214)) = literalRow1017 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 210
  · have hj : j = (⟨210, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1017]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d253_s2_row1017_col210
  by_cases h1 : j.val = 211
  · have hj : j = (⟨211, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1017, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk32.cell_d254_s0_row1017_col211
  by_cases h2 : j.val = 212
  · have hj : j = (⟨212, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow1017, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk32.cell_d254_s2_row1017_col212
  by_cases h3 : j.val = 213
  · have hj : j = (⟨213, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow1017, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (245 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk32.cell_d254_s1_row1017_col213
  · simp [literalRow1017, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk52.row1017_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row1017

def literalRow1019 (j : Fin 222) : M := if j.val = 211 then 5 else if j.val = 212 then 7 else if j.val = 213 then 2147483642 else 0

theorem literalSourceMatrix_row1019 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨212, by decide⟩ : Fin 214)) = literalRow1019 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 211
  · have hj : j = (⟨211, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1019]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1019 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk32.cell_d254_s0_row1019_col211
  by_cases h1 : j.val = 212
  · have hj : j = (⟨212, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1019, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1019 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk32.cell_d254_s2_row1019_col212
  by_cases h2 : j.val = 213
  · have hj : j = (⟨213, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow1019, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1019 = (2147483642 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk32.cell_d254_s1_row1019_col213
  · simp [literalRow1019, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk52.row1019_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row1019

end
end AspisV8R19.R804LiteralSourceRowsChunk52
