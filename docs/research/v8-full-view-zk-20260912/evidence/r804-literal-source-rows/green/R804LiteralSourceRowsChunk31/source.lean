import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk14
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk31
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk31
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow380 (j : Fin 222) : M := if j.val = 123 then 1073741826 else if j.val = 124 then 1073741826 else if j.val = 125 then 1073741772 else if j.val = 126 then 1073741483 else 0

theorem literalSourceMatrix_row380 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨125, by decide⟩ : Fin 214)) = literalRow380 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 123
  · have hj : j = (⟨123, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow380]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨94, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 380 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d94_s0_row380_col123
  by_cases h1 : j.val = 124
  · have hj : j = (⟨124, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow380, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨94, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 380 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d94_s1_row380_col124
  by_cases h2 : j.val = 125
  · have hj : j = (⟨125, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow380, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨95, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 380 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d95_s0_row380_col125
  by_cases h3 : j.val = 126
  · have hj : j = (⟨126, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow380, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨95, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 380 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d95_s1_row380_col126
  · simp [literalRow380, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk31.row380_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row380

def literalRow382 (j : Fin 222) : M := if j.val = 125 then 2147483612 else if j.val = 126 then 2147483409 else 0

theorem literalSourceMatrix_row382 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨126, by decide⟩ : Fin 214)) = literalRow382 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 125
  · have hj : j = (⟨125, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow382]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨95, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 382 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d95_s0_row382_col125
  by_cases h1 : j.val = 126
  · have hj : j = (⟨126, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow382, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨95, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 382 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d95_s1_row382_col126
  · simp [literalRow382, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk31.row382_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row382

def literalRow499 (j : Fin 222) : M := if j.val = 127 then 7 else 0

theorem literalSourceMatrix_row499 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨127, by decide⟩ : Fin 214)) = literalRow499 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 127
  · have hj : j = (⟨127, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow499]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨124, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 499 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d124_s2_row499_col127
  · simp [literalRow499, h0]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk31.row499_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact h0 hm
#print axioms literalSourceMatrix_row499

def literalRow501 (j : Fin 222) : M := if j.val = 127 then 1073741826 else if j.val = 128 then 42 else if j.val = 129 then 1073743541 else 0

theorem literalSourceMatrix_row501 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨128, by decide⟩ : Fin 214)) = literalRow501 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 127
  · have hj : j = (⟨127, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow501]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨124, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 501 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d124_s2_row501_col127
  by_cases h1 : j.val = 128
  · have hj : j = (⟨128, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow501, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨125, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 501 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d125_s0_row501_col128
  by_cases h2 : j.val = 129
  · have hj : j = (⟨129, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow501, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 501 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d125_s2_row501_col129
  · simp [literalRow501, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk31.row501_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row501

end
end AspisV8R19.R804LiteralSourceRowsChunk31
