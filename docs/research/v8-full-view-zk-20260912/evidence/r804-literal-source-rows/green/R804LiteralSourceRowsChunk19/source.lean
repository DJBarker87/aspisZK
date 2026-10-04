import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk05
import AspisV8R19.R799ActiveSourceCellsChunk06
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk19
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk19
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow279 (j : Fin 222) : M := if j.val = 76 then 5 else if j.val = 77 then 7 else 0

theorem literalSourceMatrix_row279 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨77, by decide⟩ : Fin 214)) = literalRow279 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 76
  · have hj : j = (⟨76, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow279]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 279 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d69_s0_row279_col76
  by_cases h1 : j.val = 77
  · have hj : j = (⟨77, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow279, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 279 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d69_s2_row279_col77
  · simp [literalRow279, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk19.row279_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row279

def literalRow281 (j : Fin 222) : M := if j.val = 77 then 536870913 else if j.val = 78 then 42 else if j.val = 79 then 1073743541 else if j.val = 81 then 536870913 else 0

theorem literalSourceMatrix_row281 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨78, by decide⟩ : Fin 214)) = literalRow281 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 77
  · have hj : j = (⟨77, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow281]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d69_s2_row281_col77
  by_cases h1 : j.val = 78
  · have hj : j = (⟨78, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow281, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d70_s0_row281_col78
  by_cases h2 : j.val = 79
  · have hj : j = (⟨79, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow281, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d70_s2_row281_col79
  by_cases h3 : j.val = 81
  · have hj : j = (⟨81, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow281, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d71_s2_row281_col81
  · simp [literalRow281, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk19.row281_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row281

def literalRow283 (j : Fin 222) : M := if j.val = 78 then 5 else if j.val = 79 then 7 else 0

theorem literalSourceMatrix_row283 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨79, by decide⟩ : Fin 214)) = literalRow283 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 78
  · have hj : j = (⟨78, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow283]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 283 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d70_s0_row283_col78
  by_cases h1 : j.val = 79
  · have hj : j = (⟨79, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow283, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 283 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d70_s2_row283_col79
  · simp [literalRow283, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk19.row283_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row283

def literalRow285 (j : Fin 222) : M := if j.val = 79 then 1073741826 else if j.val = 80 then 42 else if j.val = 81 then 1073743541 else 0

theorem literalSourceMatrix_row285 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨80, by decide⟩ : Fin 214)) = literalRow285 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 79
  · have hj : j = (⟨79, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow285]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 285 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d70_s2_row285_col79
  by_cases h1 : j.val = 80
  · have hj : j = (⟨80, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow285, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 285 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d71_s0_row285_col80
  by_cases h2 : j.val = 81
  · have hj : j = (⟨81, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow285, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 285 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d71_s2_row285_col81
  · simp [literalRow285, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk19.row285_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row285

end
end AspisV8R19.R804LiteralSourceRowsChunk19
