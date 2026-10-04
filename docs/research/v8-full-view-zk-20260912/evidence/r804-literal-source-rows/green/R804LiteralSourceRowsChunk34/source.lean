import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk16
import AspisV8R19.R799ActiveSourceCellsChunk17
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk34
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk34
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow632 (j : Fin 222) : M := if j.val = 135 then 536870913 else if j.val = 136 then 536870913 else if j.val = 137 then 1073741772 else if j.val = 138 then 1073741483 else if j.val = 139 then 536870913 else if j.val = 140 then 536870913 else 0

theorem literalSourceMatrix_row632 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨137, by decide⟩ : Fin 214)) = literalRow632 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 135
  · have hj : j = (⟨135, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow632]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 632 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d157_s0_row632_col135
  by_cases h1 : j.val = 136
  · have hj : j = (⟨136, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow632, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 632 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d157_s1_row632_col136
  by_cases h2 : j.val = 137
  · have hj : j = (⟨137, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow632, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨158, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 632 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d158_s0_row632_col137
  by_cases h3 : j.val = 138
  · have hj : j = (⟨138, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow632, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨158, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 632 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d158_s1_row632_col138
  by_cases h4 : j.val = 139
  · have hj : j = (⟨139, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow632, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 632 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d159_s0_row632_col139
  by_cases h5 : j.val = 140
  · have hj : j = (⟨140, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow632, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 632 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d159_s1_row632_col140
  · simp [literalRow632, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk34.row632_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row632

def literalRow634 (j : Fin 222) : M := if j.val = 137 then 2147483612 else if j.val = 138 then 2147483409 else if j.val = 141 then 536870913 else 0

theorem literalSourceMatrix_row634 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨138, by decide⟩ : Fin 214)) = literalRow634 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 137
  · have hj : j = (⟨137, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow634]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨158, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 634 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d158_s0_row634_col137
  by_cases h1 : j.val = 138
  · have hj : j = (⟨138, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow634, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨158, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 634 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d158_s1_row634_col138
  by_cases h2 : j.val = 141
  · have hj : j = (⟨141, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow634, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 634 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d159_s2_row634_col141
  · simp [literalRow634, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk34.row634_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row634

def literalRow636 (j : Fin 222) : M := if j.val = 137 then 1073741826 else if j.val = 138 then 1073741826 else if j.val = 139 then 1073741772 else if j.val = 140 then 1073741483 else if j.val = 141 then 2147481246 else 0

theorem literalSourceMatrix_row636 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨139, by decide⟩ : Fin 214)) = literalRow636 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 137
  · have hj : j = (⟨137, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow636]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨158, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 636 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d158_s0_row636_col137
  by_cases h1 : j.val = 138
  · have hj : j = (⟨138, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow636, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨158, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 636 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d158_s1_row636_col138
  by_cases h2 : j.val = 139
  · have hj : j = (⟨139, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow636, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 636 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d159_s0_row636_col139
  by_cases h3 : j.val = 140
  · have hj : j = (⟨140, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow636, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 636 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d159_s1_row636_col140
  by_cases h4 : j.val = 141
  · have hj : j = (⟨141, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow636, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 636 = (2147481246 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d159_s2_row636_col141
  · simp [literalRow636, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk34.row636_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row636

def literalRow638 (j : Fin 222) : M := if j.val = 139 then 2147483612 else if j.val = 140 then 2147483409 else if j.val = 141 then 1073740106 else 0

theorem literalSourceMatrix_row638 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨140, by decide⟩ : Fin 214)) = literalRow638 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 139
  · have hj : j = (⟨139, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow638]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 638 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d159_s0_row638_col139
  by_cases h1 : j.val = 140
  · have hj : j = (⟨140, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow638, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 638 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d159_s1_row638_col140
  by_cases h2 : j.val = 141
  · have hj : j = (⟨141, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow638, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 638 = (1073740106 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d159_s2_row638_col141
  · simp [literalRow638, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk34.row638_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row638

end
end AspisV8R19.R804LiteralSourceRowsChunk34
