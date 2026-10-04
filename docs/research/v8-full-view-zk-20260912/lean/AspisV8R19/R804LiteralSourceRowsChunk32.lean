import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk14
import AspisV8R19.R799ActiveSourceCellsChunk15
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk32
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk32
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow503 (j : Fin 222) : M := if j.val = 128 then 5 else if j.val = 129 then 7 else 0

theorem literalSourceMatrix_row503 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨129, by decide⟩ : Fin 214)) = literalRow503 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 128
  · have hj : j = (⟨128, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow503]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨125, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 503 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d125_s0_row503_col128
  by_cases h1 : j.val = 129
  · have hj : j = (⟨129, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow503, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 503 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d125_s2_row503_col129
  · simp [literalRow503, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk32.row503_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row503

def literalRow505 (j : Fin 222) : M := if j.val = 129 then 536870913 else if j.val = 130 then 42 else if j.val = 131 then 1073743541 else if j.val = 133 then 536870913 else 0

theorem literalSourceMatrix_row505 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨130, by decide⟩ : Fin 214)) = literalRow505 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 129
  · have hj : j = (⟨129, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow505]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d125_s2_row505_col129
  by_cases h1 : j.val = 130
  · have hj : j = (⟨130, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow505, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d126_s0_row505_col130
  by_cases h2 : j.val = 131
  · have hj : j = (⟨131, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow505, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d126_s2_row505_col131
  by_cases h3 : j.val = 133
  · have hj : j = (⟨133, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow505, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d127_s2_row505_col133
  · simp [literalRow505, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk32.row505_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row505

def literalRow507 (j : Fin 222) : M := if j.val = 130 then 5 else if j.val = 131 then 7 else 0

theorem literalSourceMatrix_row507 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨131, by decide⟩ : Fin 214)) = literalRow507 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 130
  · have hj : j = (⟨130, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow507]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 507 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d126_s0_row507_col130
  by_cases h1 : j.val = 131
  · have hj : j = (⟨131, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow507, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 507 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d126_s2_row507_col131
  · simp [literalRow507, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk32.row507_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row507

def literalRow509 (j : Fin 222) : M := if j.val = 131 then 1073741826 else if j.val = 132 then 42 else if j.val = 133 then 1073743541 else 0

theorem literalSourceMatrix_row509 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨132, by decide⟩ : Fin 214)) = literalRow509 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 131
  · have hj : j = (⟨131, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow509]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 509 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d126_s2_row509_col131
  by_cases h1 : j.val = 132
  · have hj : j = (⟨132, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow509, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 509 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d127_s0_row509_col132
  by_cases h2 : j.val = 133
  · have hj : j = (⟨133, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow509, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 509 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk15.cell_d127_s2_row509_col133
  · simp [literalRow509, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk32.row509_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row509

end
end AspisV8R19.R804LiteralSourceRowsChunk32
