import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk10
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk25
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk25
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow329 (j : Fin 222) : M := if j.val = 100 then 536870913 else if j.val = 101 then 42 else if j.val = 102 then 1073743541 else if j.val = 104 then 536870913 else 0

theorem literalSourceMatrix_row329 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨101, by decide⟩ : Fin 214)) = literalRow329 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 100
  · have hj : j = (⟨100, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow329]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 329 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d81_s2_row329_col100
  by_cases h1 : j.val = 101
  · have hj : j = (⟨101, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow329, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨82, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 329 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d82_s0_row329_col101
  by_cases h2 : j.val = 102
  · have hj : j = (⟨102, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow329, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨82, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 329 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d82_s2_row329_col102
  by_cases h3 : j.val = 104
  · have hj : j = (⟨104, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow329, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 329 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d83_s2_row329_col104
  · simp [literalRow329, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk25.row329_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row329

def literalRow331 (j : Fin 222) : M := if j.val = 101 then 5 else if j.val = 102 then 7 else 0

theorem literalSourceMatrix_row331 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨102, by decide⟩ : Fin 214)) = literalRow331 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 101
  · have hj : j = (⟨101, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow331]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨82, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 331 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d82_s0_row331_col101
  by_cases h1 : j.val = 102
  · have hj : j = (⟨102, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow331, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨82, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 331 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d82_s2_row331_col102
  · simp [literalRow331, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk25.row331_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row331

def literalRow333 (j : Fin 222) : M := if j.val = 102 then 1073741826 else if j.val = 103 then 42 else if j.val = 104 then 1073743541 else 0

theorem literalSourceMatrix_row333 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨103, by decide⟩ : Fin 214)) = literalRow333 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 102
  · have hj : j = (⟨102, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow333]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨82, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 333 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d82_s2_row333_col102
  by_cases h1 : j.val = 103
  · have hj : j = (⟨103, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow333, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 333 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d83_s0_row333_col103
  by_cases h2 : j.val = 104
  · have hj : j = (⟨104, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow333, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 333 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d83_s2_row333_col104
  · simp [literalRow333, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk25.row333_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row333

def literalRow335 (j : Fin 222) : M := if j.val = 103 then 5 else if j.val = 104 then 7 else 0

theorem literalSourceMatrix_row335 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨104, by decide⟩ : Fin 214)) = literalRow335 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 103
  · have hj : j = (⟨103, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow335]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 335 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d83_s0_row335_col103
  by_cases h1 : j.val = 104
  · have hj : j = (⟨104, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow335, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 335 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk10.cell_d83_s2_row335_col104
  · simp [literalRow335, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk25.row335_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row335

end
end AspisV8R19.R804LiteralSourceRowsChunk25
