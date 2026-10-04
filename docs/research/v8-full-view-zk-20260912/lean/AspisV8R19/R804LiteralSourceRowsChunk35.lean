import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk17
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk35
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk35
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow639 (j : Fin 222) : M := if j.val = 139 then 5 else if j.val = 140 then 2147483642 else if j.val = 141 then 7 else 0

theorem literalSourceMatrix_row639 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨141, by decide⟩ : Fin 214)) = literalRow639 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 139
  · have hj : j = (⟨139, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow639]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 639 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d159_s0_row639_col139
  by_cases h1 : j.val = 140
  · have hj : j = (⟨140, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow639, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 639 = (2147483642 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d159_s1_row639_col140
  by_cases h2 : j.val = 141
  · have hj : j = (⟨141, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow639, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 639 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d159_s2_row639_col141
  · simp [literalRow639, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk35.row639_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row639

def literalRow755 (j : Fin 222) : M := if j.val = 142 then 7 else 0

theorem literalSourceMatrix_row755 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨142, by decide⟩ : Fin 214)) = literalRow755 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 142
  · have hj : j = (⟨142, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow755]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 755 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d188_s2_row755_col142
  · simp [literalRow755, h0]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk35.row755_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact h0 hm
#print axioms literalSourceMatrix_row755

def literalRow757 (j : Fin 222) : M := if j.val = 142 then 1073741826 else if j.val = 143 then 42 else if j.val = 144 then 1073743541 else 0

theorem literalSourceMatrix_row757 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨143, by decide⟩ : Fin 214)) = literalRow757 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 142
  · have hj : j = (⟨142, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow757]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 757 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d188_s2_row757_col142
  by_cases h1 : j.val = 143
  · have hj : j = (⟨143, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow757, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 757 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d189_s0_row757_col143
  by_cases h2 : j.val = 144
  · have hj : j = (⟨144, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow757, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 757 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d189_s2_row757_col144
  · simp [literalRow757, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk35.row757_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row757

def literalRow759 (j : Fin 222) : M := if j.val = 143 then 5 else if j.val = 144 then 7 else 0

theorem literalSourceMatrix_row759 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨144, by decide⟩ : Fin 214)) = literalRow759 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 143
  · have hj : j = (⟨143, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow759]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 759 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d189_s0_row759_col143
  by_cases h1 : j.val = 144
  · have hj : j = (⟨144, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow759, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 759 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d189_s2_row759_col144
  · simp [literalRow759, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk35.row759_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row759

end
end AspisV8R19.R804LiteralSourceRowsChunk35
