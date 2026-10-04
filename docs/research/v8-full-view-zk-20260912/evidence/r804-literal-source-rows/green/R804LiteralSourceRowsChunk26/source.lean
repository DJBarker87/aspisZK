import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk10
import AspisV8R19.R799ActiveSourceCellsChunk11
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk26
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk26
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow337 (j : Fin 222) : M := if j.val = 104 then 1342177280 else if j.val = 105 then 42 else if j.val = 106 then 1073743541 else if j.val = 108 then 536870913 else if j.val = 112 then 1342177280 else 0

theorem literalSourceMatrix_row337 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨105, by decide⟩ : Fin 214)) = literalRow337 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 104
  · have hj : j = (⟨104, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow337]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 337 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d83_s2_row337_col104
  by_cases h1 : j.val = 105
  · have hj : j = (⟨105, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow337, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 337 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d84_s0_row337_col105
  by_cases h2 : j.val = 106
  · have hj : j = (⟨106, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow337, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 337 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d84_s2_row337_col106
  by_cases h3 : j.val = 108
  · have hj : j = (⟨108, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow337, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 337 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d85_s2_row337_col108
  by_cases h4 : j.val = 112
  · have hj : j = (⟨112, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow337, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 337 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d87_s2_row337_col112
  · simp [literalRow337, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk26.row337_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row337

def literalRow339 (j : Fin 222) : M := if j.val = 105 then 5 else if j.val = 106 then 7 else 0

theorem literalSourceMatrix_row339 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨106, by decide⟩ : Fin 214)) = literalRow339 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 105
  · have hj : j = (⟨105, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow339]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 339 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d84_s0_row339_col105
  by_cases h1 : j.val = 106
  · have hj : j = (⟨106, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow339, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 339 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d84_s2_row339_col106
  · simp [literalRow339, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk26.row339_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row339

def literalRow341 (j : Fin 222) : M := if j.val = 106 then 1073741826 else if j.val = 107 then 42 else if j.val = 108 then 1073743541 else 0

theorem literalSourceMatrix_row341 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨107, by decide⟩ : Fin 214)) = literalRow341 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 106
  · have hj : j = (⟨106, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow341]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 341 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d84_s2_row341_col106
  by_cases h1 : j.val = 107
  · have hj : j = (⟨107, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow341, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 341 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d85_s0_row341_col107
  by_cases h2 : j.val = 108
  · have hj : j = (⟨108, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow341, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 341 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d85_s2_row341_col108
  · simp [literalRow341, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk26.row341_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row341

def literalRow343 (j : Fin 222) : M := if j.val = 107 then 5 else if j.val = 108 then 7 else 0

theorem literalSourceMatrix_row343 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨108, by decide⟩ : Fin 214)) = literalRow343 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 107
  · have hj : j = (⟨107, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow343]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 343 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d85_s0_row343_col107
  by_cases h1 : j.val = 108
  · have hj : j = (⟨108, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow343, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 343 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk11.cell_d85_s2_row343_col108
  · simp [literalRow343, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk26.row343_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row343

end
end AspisV8R19.R804LiteralSourceRowsChunk26
