import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk11
import AspisV8R19.R799ActiveSourceCellsChunk12
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk27
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk27
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow345 (j : Fin 222) : M := if j.val = 108 then 536870913 else if j.val = 109 then 42 else if j.val = 110 then 1073743541 else if j.val = 112 then 536870913 else 0

theorem literalSourceMatrix_row345 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨109, by decide⟩ : Fin 214)) = literalRow345 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 108
  · have hj : j = (⟨108, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow345]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d85_s2_row345_col108
  by_cases h1 : j.val = 109
  · have hj : j = (⟨109, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow345, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d86_s0_row345_col109
  by_cases h2 : j.val = 110
  · have hj : j = (⟨110, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow345, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d86_s2_row345_col110
  by_cases h3 : j.val = 112
  · have hj : j = (⟨112, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow345, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d87_s2_row345_col112
  · simp [literalRow345, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk27.row345_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row345

def literalRow347 (j : Fin 222) : M := if j.val = 109 then 5 else if j.val = 110 then 7 else 0

theorem literalSourceMatrix_row347 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨110, by decide⟩ : Fin 214)) = literalRow347 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 109
  · have hj : j = (⟨109, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow347]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 347 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d86_s0_row347_col109
  by_cases h1 : j.val = 110
  · have hj : j = (⟨110, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow347, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 347 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d86_s2_row347_col110
  · simp [literalRow347, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk27.row347_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row347

def literalRow349 (j : Fin 222) : M := if j.val = 110 then 1073741826 else if j.val = 111 then 42 else if j.val = 112 then 1073743541 else 0

theorem literalSourceMatrix_row349 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨111, by decide⟩ : Fin 214)) = literalRow349 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 110
  · have hj : j = (⟨110, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow349]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 349 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d86_s2_row349_col110
  by_cases h1 : j.val = 111
  · have hj : j = (⟨111, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow349, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 349 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d87_s0_row349_col111
  by_cases h2 : j.val = 112
  · have hj : j = (⟨112, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow349, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 349 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d87_s2_row349_col112
  · simp [literalRow349, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk27.row349_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row349

def literalRow351 (j : Fin 222) : M := if j.val = 111 then 5 else if j.val = 112 then 7 else 0

theorem literalSourceMatrix_row351 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨112, by decide⟩ : Fin 214)) = literalRow351 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 111
  · have hj : j = (⟨111, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow351]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 351 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d87_s0_row351_col111
  by_cases h1 : j.val = 112
  · have hj : j = (⟨112, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow351, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 351 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d87_s2_row351_col112
  · simp [literalRow351, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk27.row351_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row351

end
end AspisV8R19.R804LiteralSourceRowsChunk27
