import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk08
import AspisV8R19.R799ActiveSourceCellsChunk09
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk23
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk23
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow313 (j : Fin 222) : M := if j.val = 92 then 536870913 else if j.val = 93 then 42 else if j.val = 94 then 1073743541 else if j.val = 96 then 536870913 else 0

theorem literalSourceMatrix_row313 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨93, by decide⟩ : Fin 214)) = literalRow313 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 92
  · have hj : j = (⟨92, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow313]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d77_s2_row313_col92
  by_cases h1 : j.val = 93
  · have hj : j = (⟨93, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow313, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d78_s0_row313_col93
  by_cases h2 : j.val = 94
  · have hj : j = (⟨94, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow313, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d78_s2_row313_col94
  by_cases h3 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow313, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d79_s2_row313_col96
  · simp [literalRow313, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk23.row313_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row313

def literalRow315 (j : Fin 222) : M := if j.val = 93 then 5 else if j.val = 94 then 7 else 0

theorem literalSourceMatrix_row315 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨94, by decide⟩ : Fin 214)) = literalRow315 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 93
  · have hj : j = (⟨93, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow315]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 315 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d78_s0_row315_col93
  by_cases h1 : j.val = 94
  · have hj : j = (⟨94, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow315, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 315 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d78_s2_row315_col94
  · simp [literalRow315, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk23.row315_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row315

def literalRow317 (j : Fin 222) : M := if j.val = 94 then 1073741826 else if j.val = 95 then 42 else if j.val = 96 then 1073743541 else 0

theorem literalSourceMatrix_row317 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨95, by decide⟩ : Fin 214)) = literalRow317 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 94
  · have hj : j = (⟨94, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow317]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 317 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d78_s2_row317_col94
  by_cases h1 : j.val = 95
  · have hj : j = (⟨95, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow317, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 317 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d79_s0_row317_col95
  by_cases h2 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow317, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 317 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d79_s2_row317_col96
  · simp [literalRow317, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk23.row317_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row317

def literalRow319 (j : Fin 222) : M := if j.val = 95 then 5 else if j.val = 96 then 7 else 0

theorem literalSourceMatrix_row319 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨96, by decide⟩ : Fin 214)) = literalRow319 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 95
  · have hj : j = (⟨95, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow319]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 319 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d79_s0_row319_col95
  by_cases h1 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow319, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 319 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk09.cell_d79_s2_row319_col96
  · simp [literalRow319, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk23.row319_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row319

end
end AspisV8R19.R804LiteralSourceRowsChunk23
