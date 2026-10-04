import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsPreflight
import AspisV8R19.R799ActiveSourceCellsChunk02
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk14
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk14
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow236 (j : Fin 222) : M := if j.val = 55 then 1073741826 else if j.val = 56 then 1073741826 else if j.val = 57 then 1073741772 else if j.val = 58 then 1073741483 else 0

theorem literalSourceMatrix_row236 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨57, by decide⟩ : Fin 214)) = literalRow236 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 55
  · have hj : j = (⟨55, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow236]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 236 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d58_s0_row236_col55
  by_cases h1 : j.val = 56
  · have hj : j = (⟨56, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow236, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 236 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d58_s1_row236_col56
  by_cases h2 : j.val = 57
  · have hj : j = (⟨57, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow236, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 236 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d59_s0_row236_col57
  by_cases h3 : j.val = 58
  · have hj : j = (⟨58, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow236, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 236 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d59_s1_row236_col58
  · simp [literalRow236, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk14.row236_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row236

def literalRow238 (j : Fin 222) : M := if j.val = 57 then 2147483612 else if j.val = 58 then 2147483409 else 0

theorem literalSourceMatrix_row238 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨58, by decide⟩ : Fin 214)) = literalRow238 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 57
  · have hj : j = (⟨57, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow238]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 238 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d59_s0_row238_col57
  by_cases h1 : j.val = 58
  · have hj : j = (⟨58, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow238, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 238 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d59_s1_row238_col58
  · simp [literalRow238, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk14.row238_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row238

def literalRow240 (j : Fin 222) : M := if j.val = 57 then 1342177280 else if j.val = 58 then 1342177280 else if j.val = 59 then 1073741772 else if j.val = 60 then 2147481246 else if j.val = 61 then 536870913 else if j.val = 65 then 1342177280 else 0

theorem literalSourceMatrix_row240 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨59, by decide⟩ : Fin 214)) = literalRow240 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 57
  · have hj : j = (⟨57, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow240]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 240 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d59_s0_row240_col57
  by_cases h1 : j.val = 58
  · have hj : j = (⟨58, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow240, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 240 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d59_s1_row240_col58
  by_cases h2 : j.val = 59
  · have hj : j = (⟨59, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow240, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 240 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d60_s0_row240_col59
  by_cases h3 : j.val = 60
  · have hj : j = (⟨60, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow240, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨60, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 240 = (2147481246 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d60_s2_row240_col60
  by_cases h4 : j.val = 61
  · have hj : j = (⟨61, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow240, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 240 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d61_s0_row240_col61
  by_cases h5 : j.val = 65
  · have hj : j = (⟨65, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow240, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 240 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d63_s0_row240_col65
  · simp [literalRow240, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk14.row240_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row240

def literalRow243 (j : Fin 222) : M := if j.val = 59 then 5 else if j.val = 60 then 7 else 0

theorem literalSourceMatrix_row243 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨60, by decide⟩ : Fin 214)) = literalRow243 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 59
  · have hj : j = (⟨59, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow243]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 243 = (5 : M)
    exact AspisV8R19.R797ActiveSourceCellsPreflight.cell_d60_s0_row243
  by_cases h1 : j.val = 60
  · have hj : j = (⟨60, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow243, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨60, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 243 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d60_s2_row243_col60
  · simp [literalRow243, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk14.row243_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row243

end
end AspisV8R19.R804LiteralSourceRowsChunk14
