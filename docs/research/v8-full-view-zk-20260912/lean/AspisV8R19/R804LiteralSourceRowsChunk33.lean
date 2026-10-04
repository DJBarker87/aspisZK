import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk15
import AspisV8R19.R799ActiveSourceCellsChunk16
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk33
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk33
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow511 (j : Fin 222) : M := if j.val = 132 then 5 else if j.val = 133 then 7 else 0

theorem literalSourceMatrix_row511 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨133, by decide⟩ : Fin 214)) = literalRow511 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 132
  · have hj : j = (⟨132, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow511]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 511 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d127_s0_row511_col132
  by_cases h1 : j.val = 133
  · have hj : j = (⟨133, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow511, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 511 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d127_s2_row511_col133
  · simp [literalRow511, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk33.row511_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row511

def literalRow626 (j : Fin 222) : M := if j.val = 134 then 2147483409 else if j.val = 141 then 1342177280 else 0

theorem literalSourceMatrix_row626 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨134, by decide⟩ : Fin 214)) = literalRow626 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 134
  · have hj : j = (⟨134, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow626]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 626 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d156_s1_row626_col134
  by_cases h1 : j.val = 141
  · have hj : j = (⟨141, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow626, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 626 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d159_s2_row626_col141
  · simp [literalRow626, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk33.row626_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row626

def literalRow628 (j : Fin 222) : M := if j.val = 134 then 1073741826 else if j.val = 135 then 1073741772 else if j.val = 136 then 1073741483 else 0

theorem literalSourceMatrix_row628 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨135, by decide⟩ : Fin 214)) = literalRow628 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 134
  · have hj : j = (⟨134, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow628]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 628 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d156_s1_row628_col134
  by_cases h1 : j.val = 135
  · have hj : j = (⟨135, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow628, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 628 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d157_s0_row628_col135
  by_cases h2 : j.val = 136
  · have hj : j = (⟨136, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow628, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 628 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d157_s1_row628_col136
  · simp [literalRow628, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk33.row628_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row628

def literalRow630 (j : Fin 222) : M := if j.val = 135 then 2147483612 else if j.val = 136 then 2147483409 else 0

theorem literalSourceMatrix_row630 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨136, by decide⟩ : Fin 214)) = literalRow630 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 135
  · have hj : j = (⟨135, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow630]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 630 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d157_s0_row630_col135
  by_cases h1 : j.val = 136
  · have hj : j = (⟨136, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow630, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 630 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk16.cell_d157_s1_row630_col136
  · simp [literalRow630, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk33.row630_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row630

end
end AspisV8R19.R804LiteralSourceRowsChunk33
