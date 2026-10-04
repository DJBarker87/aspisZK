import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk09
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk24
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk24
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow321 (j : Fin 222) : M := if j.val = 96 then 335544320 else if j.val = 97 then 42 else if j.val = 98 then 1073743541 else if j.val = 100 then 536870913 else if j.val = 104 then 1342177280 else if j.val = 112 then 671088640 else 0

theorem literalSourceMatrix_row321 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨97, by decide⟩ : Fin 214)) = literalRow321 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow321]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (335544320 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d79_s2_row321_col96
  by_cases h1 : j.val = 97
  · have hj : j = (⟨97, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow321, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d80_s0_row321_col97
  by_cases h2 : j.val = 98
  · have hj : j = (⟨98, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow321, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d80_s2_row321_col98
  by_cases h3 : j.val = 100
  · have hj : j = (⟨100, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow321, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d81_s2_row321_col100
  by_cases h4 : j.val = 104
  · have hj : j = (⟨104, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow321, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d83_s2_row321_col104
  by_cases h5 : j.val = 112
  · have hj : j = (⟨112, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow321, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d87_s2_row321_col112
  · simp [literalRow321, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk24.row321_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row321

def literalRow323 (j : Fin 222) : M := if j.val = 97 then 5 else if j.val = 98 then 7 else 0

theorem literalSourceMatrix_row323 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨98, by decide⟩ : Fin 214)) = literalRow323 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 97
  · have hj : j = (⟨97, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow323]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 323 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d80_s0_row323_col97
  by_cases h1 : j.val = 98
  · have hj : j = (⟨98, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow323, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 323 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d80_s2_row323_col98
  · simp [literalRow323, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk24.row323_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row323

def literalRow325 (j : Fin 222) : M := if j.val = 98 then 1073741826 else if j.val = 99 then 42 else if j.val = 100 then 1073743541 else 0

theorem literalSourceMatrix_row325 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨99, by decide⟩ : Fin 214)) = literalRow325 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 98
  · have hj : j = (⟨98, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow325]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 325 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d80_s2_row325_col98
  by_cases h1 : j.val = 99
  · have hj : j = (⟨99, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow325, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 325 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d81_s0_row325_col99
  by_cases h2 : j.val = 100
  · have hj : j = (⟨100, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow325, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 325 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d81_s2_row325_col100
  · simp [literalRow325, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk24.row325_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row325

def literalRow327 (j : Fin 222) : M := if j.val = 99 then 5 else if j.val = 100 then 7 else 0

theorem literalSourceMatrix_row327 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨100, by decide⟩ : Fin 214)) = literalRow327 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 99
  · have hj : j = (⟨99, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow327]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 327 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d81_s0_row327_col99
  by_cases h1 : j.val = 100
  · have hj : j = (⟨100, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow327, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 327 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d81_s2_row327_col100
  · simp [literalRow327, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk24.row327_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row327

end
end AspisV8R19.R804LiteralSourceRowsChunk24
