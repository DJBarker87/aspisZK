import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk19
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk38
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk38
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow890 (j : Fin 222) : M := if j.val = 152 then 2147483612 else if j.val = 153 then 2147483409 else 0

theorem literalSourceMatrix_row890 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨153, by decide⟩ : Fin 214)) = literalRow890 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 152
  · have hj : j = (⟨152, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow890]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨222, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 890 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d222_s0_row890_col152
  by_cases h1 : j.val = 153
  · have hj : j = (⟨153, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow890, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨222, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 890 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d222_s1_row890_col153
  · simp [literalRow890, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk38.row890_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row890

def literalRow892 (j : Fin 222) : M := if j.val = 152 then 1073741826 else if j.val = 153 then 1073741826 else if j.val = 154 then 1073741772 else if j.val = 155 then 1073741483 else 0

theorem literalSourceMatrix_row892 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨154, by decide⟩ : Fin 214)) = literalRow892 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 152
  · have hj : j = (⟨152, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow892]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨222, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 892 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d222_s0_row892_col152
  by_cases h1 : j.val = 153
  · have hj : j = (⟨153, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow892, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨222, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 892 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d222_s1_row892_col153
  by_cases h2 : j.val = 154
  · have hj : j = (⟨154, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow892, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨223, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 892 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d223_s0_row892_col154
  by_cases h3 : j.val = 155
  · have hj : j = (⟨155, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow892, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨223, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 892 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d223_s1_row892_col155
  · simp [literalRow892, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk38.row892_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row892

def literalRow894 (j : Fin 222) : M := if j.val = 154 then 2147483612 else if j.val = 155 then 2147483409 else 0

theorem literalSourceMatrix_row894 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨155, by decide⟩ : Fin 214)) = literalRow894 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 154
  · have hj : j = (⟨154, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow894]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨223, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 894 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d223_s0_row894_col154
  by_cases h1 : j.val = 155
  · have hj : j = (⟨155, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow894, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨223, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 894 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d223_s1_row894_col155
  · simp [literalRow894, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk38.row894_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row894

def literalRow900 (j : Fin 222) : M := if j.val = 156 then 1073741772 else if j.val = 157 then 1073741483 else 0

theorem literalSourceMatrix_row900 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨156, by decide⟩ : Fin 214)) = literalRow900 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 156
  · have hj : j = (⟨156, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow900]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨225, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 900 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d225_s0_row900_col156
  by_cases h1 : j.val = 157
  · have hj : j = (⟨157, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow900, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨225, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 900 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d225_s1_row900_col157
  · simp [literalRow900, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk38.row900_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row900

end
end AspisV8R19.R804LiteralSourceRowsChunk38
