import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk17
import AspisV8R19.R799ActiveSourceCellsChunk18
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk36
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk36
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow761 (j : Fin 222) : M := if j.val = 144 then 536870913 else if j.val = 145 then 42 else if j.val = 146 then 1073743541 else 0

theorem literalSourceMatrix_row761 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨145, by decide⟩ : Fin 214)) = literalRow761 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 144
  · have hj : j = (⟨144, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow761]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 761 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d189_s2_row761_col144
  by_cases h1 : j.val = 145
  · have hj : j = (⟨145, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow761, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 761 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d190_s0_row761_col145
  by_cases h2 : j.val = 146
  · have hj : j = (⟨146, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow761, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 761 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d190_s2_row761_col146
  · simp [literalRow761, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk36.row761_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row761

def literalRow763 (j : Fin 222) : M := if j.val = 145 then 5 else if j.val = 146 then 7 else 0

theorem literalSourceMatrix_row763 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨146, by decide⟩ : Fin 214)) = literalRow763 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 145
  · have hj : j = (⟨145, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow763]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 763 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk17.cell_d190_s0_row763_col145
  by_cases h1 : j.val = 146
  · have hj : j = (⟨146, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow763, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 763 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d190_s2_row763_col146
  · simp [literalRow763, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk36.row763_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row763

def literalRow765 (j : Fin 222) : M := if j.val = 146 then 1073741826 else if j.val = 147 then 42 else if j.val = 148 then 245 else 0

theorem literalSourceMatrix_row765 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨147, by decide⟩ : Fin 214)) = literalRow765 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 146
  · have hj : j = (⟨146, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow765]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 765 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d190_s2_row765_col146
  by_cases h1 : j.val = 147
  · have hj : j = (⟨147, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow765, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨191, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 765 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d191_s0_row765_col147
  by_cases h2 : j.val = 148
  · have hj : j = (⟨148, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow765, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨191, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 765 = (245 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d191_s1_row765_col148
  · simp [literalRow765, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk36.row765_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row765

def literalRow766 (j : Fin 222) : M := if j.val = 146 then 1073741826 else if j.val = 147 then 2147483612 else if j.val = 148 then 2147483409 else 0

theorem literalSourceMatrix_row766 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨148, by decide⟩ : Fin 214)) = literalRow766 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 146
  · have hj : j = (⟨146, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow766]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 766 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d190_s2_row766_col146
  by_cases h1 : j.val = 147
  · have hj : j = (⟨147, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow766, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨191, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 766 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d191_s0_row766_col147
  by_cases h2 : j.val = 148
  · have hj : j = (⟨148, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow766, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨191, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 766 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d191_s1_row766_col148
  · simp [literalRow766, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk36.row766_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row766

end
end AspisV8R19.R804LiteralSourceRowsChunk36
