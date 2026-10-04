import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk06
import AspisV8R19.R799ActiveSourceCellsChunk01
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk08
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk08
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow180 (j : Fin 222) : M := if j.val = 31 then 1073741826 else if j.val = 32 then 1073741826 else if j.val = 33 then 1073741772 else 0

theorem literalSourceMatrix_row180 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨33, by decide⟩ : Fin 214)) = literalRow180 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 31
  · have hj : j = (⟨31, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow180]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 180 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d44_s0_row180_col31
  by_cases h1 : j.val = 32
  · have hj : j = (⟨32, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow180, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 180 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d44_s1_row180_col32
  by_cases h2 : j.val = 33
  · have hj : j = (⟨33, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow180, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 180 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d45_s0_row180_col33
  · simp [literalRow180, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk08.row180_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row180

def literalRow184 (j : Fin 222) : M := if j.val = 33 then 536870913 else if j.val = 34 then 1073741772 else if j.val = 35 then 536870913 else 0

theorem literalSourceMatrix_row184 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨34, by decide⟩ : Fin 214)) = literalRow184 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 33
  · have hj : j = (⟨33, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow184]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 184 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d45_s0_row184_col33
  by_cases h1 : j.val = 34
  · have hj : j = (⟨34, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow184, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 184 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d46_s0_row184_col34
  by_cases h2 : j.val = 35
  · have hj : j = (⟨35, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow184, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 184 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d47_s1_row184_col35
  · simp [literalRow184, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk08.row184_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row184

def literalRow190 (j : Fin 222) : M := if j.val = 35 then 2147483409 else if j.val = 221 then 1073740106 else 0

theorem literalSourceMatrix_row190 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨35, by decide⟩ : Fin 214)) = literalRow190 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 35
  · have hj : j = (⟨35, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow190]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 190 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d47_s1_row190_col35
  by_cases h1 : j.val = 221
  · have hj : j = (⟨221, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow190, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 190 = (1073740106 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d47_s2_row190_col221
  · simp [literalRow190, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk08.row190_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row190

def literalRow194 (j : Fin 222) : M := if j.val = 36 then 2147483409 else if j.val = 221 then 335544320 else 0

theorem literalSourceMatrix_row194 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨36, by decide⟩ : Fin 214)) = literalRow194 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 36
  · have hj : j = (⟨36, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow194]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 194 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d48_s1_row194_col36
  by_cases h1 : j.val = 221
  · have hj : j = (⟨221, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow194, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 194 = (335544320 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d47_s2_row194_col221
  · simp [literalRow194, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk08.row194_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row194

end
end AspisV8R19.R804LiteralSourceRowsChunk08
