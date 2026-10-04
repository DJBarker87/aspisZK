import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R778ActiveEntryPrototype
import AspisV8R19.R799ActiveSourceCellsChunk03
import AspisV8R19.R799ActiveSourceCellsChunk04
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk16
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk16
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow253 (j : Fin 222) : M := if j.val = 64 then 1073741826 else if j.val = 65 then 42 else 0

theorem literalSourceMatrix_row253 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨65, by decide⟩ : Fin 214)) = literalRow253 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 64
  · have hj : j = (⟨64, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow253]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 253 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d62_s2_row253_col64
  by_cases h1 : j.val = 65
  · have hj : j = (⟨65, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow253, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 253 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d63_s0_row253_col65
  · simp [literalRow253, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk16.row253_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row253

def literalRow257 (j : Fin 222) : M := if j.val = 66 then 42 else if j.val = 67 then 1073743541 else if j.val = 69 then 536870913 else if j.val = 73 then 1342177280 else if j.val = 81 then 671088640 else if j.val = 96 then 335544320 else if j.val = 133 then 83886080 else 0

theorem literalSourceMatrix_row257 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨66, by decide⟩ : Fin 214)) = literalRow257 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 66
  · have hj : j = (⟨66, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow257]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d64_s0_row257_col66
  by_cases h1 : j.val = 67
  · have hj : j = (⟨67, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow257, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d64_s2_row257_col67
  by_cases h2 : j.val = 69
  · have hj : j = (⟨69, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow257, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d65_s2_row257_col69
  by_cases h3 : j.val = 73
  · have hj : j = (⟨73, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow257, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d67_s2_row257_col73
  by_cases h4 : j.val = 81
  · have hj : j = (⟨81, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow257, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d71_s2_row257_col81
  by_cases h5 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow257, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (335544320 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d79_s2_row257_col96
  by_cases h6 : j.val = 133
  · have hj : j = (⟨133, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow257, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (83886080 : M)
    exact AspisV8R19.R778ActiveEntryPrototype.active_entry_raw_column_133_row_code_257
  · simp [literalRow257, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk16.row257_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
#print axioms literalSourceMatrix_row257

def literalRow259 (j : Fin 222) : M := if j.val = 66 then 5 else if j.val = 67 then 7 else 0

theorem literalSourceMatrix_row259 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨67, by decide⟩ : Fin 214)) = literalRow259 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 66
  · have hj : j = (⟨66, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow259]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 259 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d64_s0_row259_col66
  by_cases h1 : j.val = 67
  · have hj : j = (⟨67, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow259, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 259 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d64_s2_row259_col67
  · simp [literalRow259, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk16.row259_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row259

def literalRow261 (j : Fin 222) : M := if j.val = 67 then 1073741826 else if j.val = 68 then 42 else if j.val = 69 then 1073743541 else 0

theorem literalSourceMatrix_row261 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨68, by decide⟩ : Fin 214)) = literalRow261 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 67
  · have hj : j = (⟨67, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow261]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 261 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d64_s2_row261_col67
  by_cases h1 : j.val = 68
  · have hj : j = (⟨68, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow261, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 261 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d65_s0_row261_col68
  by_cases h2 : j.val = 69
  · have hj : j = (⟨69, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow261, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 261 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d65_s2_row261_col69
  · simp [literalRow261, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk16.row261_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row261

end
end AspisV8R19.R804LiteralSourceRowsChunk16
