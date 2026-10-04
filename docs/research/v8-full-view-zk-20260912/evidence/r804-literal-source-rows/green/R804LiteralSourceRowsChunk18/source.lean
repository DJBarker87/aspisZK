import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk04
import AspisV8R19.R799ActiveSourceCellsChunk05
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk18
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk18
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow271 (j : Fin 222) : M := if j.val = 72 then 5 else if j.val = 73 then 7 else 0

theorem literalSourceMatrix_row271 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨73, by decide⟩ : Fin 214)) = literalRow271 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 72
  · have hj : j = (⟨72, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow271]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 271 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d67_s0_row271_col72
  by_cases h1 : j.val = 73
  · have hj : j = (⟨73, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow271, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 271 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d67_s2_row271_col73
  · simp [literalRow271, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk18.row271_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row271

def literalRow273 (j : Fin 222) : M := if j.val = 73 then 1342177280 else if j.val = 74 then 42 else if j.val = 75 then 1073743541 else if j.val = 77 then 536870913 else if j.val = 81 then 1342177280 else 0

theorem literalSourceMatrix_row273 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨74, by decide⟩ : Fin 214)) = literalRow273 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 73
  · have hj : j = (⟨73, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow273]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d67_s2_row273_col73
  by_cases h1 : j.val = 74
  · have hj : j = (⟨74, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow273, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d68_s0_row273_col74
  by_cases h2 : j.val = 75
  · have hj : j = (⟨75, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow273, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d68_s2_row273_col75
  by_cases h3 : j.val = 77
  · have hj : j = (⟨77, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow273, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d69_s2_row273_col77
  by_cases h4 : j.val = 81
  · have hj : j = (⟨81, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow273, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d71_s2_row273_col81
  · simp [literalRow273, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk18.row273_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row273

def literalRow275 (j : Fin 222) : M := if j.val = 74 then 5 else if j.val = 75 then 7 else 0

theorem literalSourceMatrix_row275 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨75, by decide⟩ : Fin 214)) = literalRow275 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 74
  · have hj : j = (⟨74, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow275]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 275 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d68_s0_row275_col74
  by_cases h1 : j.val = 75
  · have hj : j = (⟨75, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow275, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 275 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d68_s2_row275_col75
  · simp [literalRow275, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk18.row275_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row275

def literalRow277 (j : Fin 222) : M := if j.val = 75 then 1073741826 else if j.val = 76 then 42 else if j.val = 77 then 1073743541 else 0

theorem literalSourceMatrix_row277 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨76, by decide⟩ : Fin 214)) = literalRow277 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 75
  · have hj : j = (⟨75, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow277]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 277 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d68_s2_row277_col75
  by_cases h1 : j.val = 76
  · have hj : j = (⟨76, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow277, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 277 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d69_s0_row277_col76
  by_cases h2 : j.val = 77
  · have hj : j = (⟨77, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow277, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 277 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk05.cell_d69_s2_row277_col77
  · simp [literalRow277, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk18.row277_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row277

end
end AspisV8R19.R804LiteralSourceRowsChunk18
