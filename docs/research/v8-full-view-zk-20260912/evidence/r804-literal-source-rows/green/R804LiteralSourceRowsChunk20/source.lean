import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk06
import AspisV8R19.R799ActiveSourceCellsChunk07
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk20
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk20
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow287 (j : Fin 222) : M := if j.val = 80 then 5 else if j.val = 81 then 7 else 0

theorem literalSourceMatrix_row287 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨81, by decide⟩ : Fin 214)) = literalRow287 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 80
  · have hj : j = (⟨80, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow287]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 287 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d71_s0_row287_col80
  by_cases h1 : j.val = 81
  · have hj : j = (⟨81, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow287, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 287 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d71_s2_row287_col81
  · simp [literalRow287, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk20.row287_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row287

def literalRow289 (j : Fin 222) : M := if j.val = 81 then 671088640 else if j.val = 82 then 42 else if j.val = 83 then 1073743541 else if j.val = 85 then 536870913 else if j.val = 89 then 1342177280 else if j.val = 96 then 671088640 else 0

theorem literalSourceMatrix_row289 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨82, by decide⟩ : Fin 214)) = literalRow289 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 81
  · have hj : j = (⟨81, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow289]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d71_s2_row289_col81
  by_cases h1 : j.val = 82
  · have hj : j = (⟨82, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow289, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d72_s0_row289_col82
  by_cases h2 : j.val = 83
  · have hj : j = (⟨83, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow289, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d72_s2_row289_col83
  by_cases h3 : j.val = 85
  · have hj : j = (⟨85, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow289, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d73_s2_row289_col85
  by_cases h4 : j.val = 89
  · have hj : j = (⟨89, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow289, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d75_s2_row289_col89
  by_cases h5 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow289, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d79_s2_row289_col96
  · simp [literalRow289, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk20.row289_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row289

def literalRow291 (j : Fin 222) : M := if j.val = 82 then 5 else if j.val = 83 then 7 else 0

theorem literalSourceMatrix_row291 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨83, by decide⟩ : Fin 214)) = literalRow291 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 82
  · have hj : j = (⟨82, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow291]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 291 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d72_s0_row291_col82
  by_cases h1 : j.val = 83
  · have hj : j = (⟨83, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow291, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 291 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk06.cell_d72_s2_row291_col83
  · simp [literalRow291, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk20.row291_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row291

def literalRow293 (j : Fin 222) : M := if j.val = 83 then 1073741826 else if j.val = 84 then 42 else if j.val = 85 then 1073743541 else 0

theorem literalSourceMatrix_row293 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨84, by decide⟩ : Fin 214)) = literalRow293 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 83
  · have hj : j = (⟨83, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow293]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 293 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d72_s2_row293_col83
  by_cases h1 : j.val = 84
  · have hj : j = (⟨84, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow293, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 293 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d73_s0_row293_col84
  by_cases h2 : j.val = 85
  · have hj : j = (⟨85, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow293, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 293 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d73_s2_row293_col85
  · simp [literalRow293, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk20.row293_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row293

end
end AspisV8R19.R804LiteralSourceRowsChunk20
