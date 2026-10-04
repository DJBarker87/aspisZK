import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk12
import AspisV8R19.R799ActiveSourceCellsChunk13
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk29
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk29
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow361 (j : Fin 222) : M := if j.val = 116 then 536870913 else if j.val = 117 then 42 else if j.val = 119 then 536870913 else 0

theorem literalSourceMatrix_row361 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨117, by decide⟩ : Fin 214)) = literalRow361 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 116
  · have hj : j = (⟨116, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow361]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 361 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d89_s2_row361_col116
  by_cases h1 : j.val = 117
  · have hj : j = (⟨117, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow361, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 361 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d90_s0_row361_col117
  by_cases h2 : j.val = 119
  · have hj : j = (⟨119, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow361, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 361 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d91_s2_row361_col119
  · simp [literalRow361, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk29.row361_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row361

def literalRow365 (j : Fin 222) : M := if j.val = 118 then 42 else if j.val = 119 then 1073743541 else 0

theorem literalSourceMatrix_row365 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨118, by decide⟩ : Fin 214)) = literalRow365 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 118
  · have hj : j = (⟨118, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow365]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 365 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d91_s0_row365_col118
  by_cases h1 : j.val = 119
  · have hj : j = (⟨119, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow365, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 365 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d91_s2_row365_col119
  · simp [literalRow365, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk29.row365_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row365

def literalRow367 (j : Fin 222) : M := if j.val = 118 then 5 else if j.val = 119 then 7 else 0

theorem literalSourceMatrix_row367 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨119, by decide⟩ : Fin 214)) = literalRow367 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 118
  · have hj : j = (⟨118, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow367]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 367 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d91_s0_row367_col118
  by_cases h1 : j.val = 119
  · have hj : j = (⟨119, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow367, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 367 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d91_s2_row367_col119
  · simp [literalRow367, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk29.row367_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row367

def literalRow370 (j : Fin 222) : M := if j.val = 119 then 1342177280 else if j.val = 120 then 2147483409 else 0

theorem literalSourceMatrix_row370 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨120, by decide⟩ : Fin 214)) = literalRow370 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 119
  · have hj : j = (⟨119, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow370]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 370 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d91_s2_row370_col119
  by_cases h1 : j.val = 120
  · have hj : j = (⟨120, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow370, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨92, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 370 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d92_s1_row370_col120
  · simp [literalRow370, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk29.row370_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row370

end
end AspisV8R19.R804LiteralSourceRowsChunk29
