import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk04
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk17
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk17
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow263 (j : Fin 222) : M := if j.val = 68 then 5 else if j.val = 69 then 7 else 0

theorem literalSourceMatrix_row263 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨69, by decide⟩ : Fin 214)) = literalRow263 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 68
  · have hj : j = (⟨68, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow263]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 263 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d65_s0_row263_col68
  by_cases h1 : j.val = 69
  · have hj : j = (⟨69, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow263, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 263 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d65_s2_row263_col69
  · simp [literalRow263, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk17.row263_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row263

def literalRow265 (j : Fin 222) : M := if j.val = 69 then 536870913 else if j.val = 70 then 42 else if j.val = 71 then 1073743541 else if j.val = 73 then 536870913 else 0

theorem literalSourceMatrix_row265 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨70, by decide⟩ : Fin 214)) = literalRow265 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 69
  · have hj : j = (⟨69, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow265]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d65_s2_row265_col69
  by_cases h1 : j.val = 70
  · have hj : j = (⟨70, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow265, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d66_s0_row265_col70
  by_cases h2 : j.val = 71
  · have hj : j = (⟨71, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow265, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d66_s2_row265_col71
  by_cases h3 : j.val = 73
  · have hj : j = (⟨73, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow265, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d67_s2_row265_col73
  · simp [literalRow265, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk17.row265_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row265

def literalRow267 (j : Fin 222) : M := if j.val = 70 then 5 else if j.val = 71 then 7 else 0

theorem literalSourceMatrix_row267 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨71, by decide⟩ : Fin 214)) = literalRow267 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 70
  · have hj : j = (⟨70, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow267]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 267 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d66_s0_row267_col70
  by_cases h1 : j.val = 71
  · have hj : j = (⟨71, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow267, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 267 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d66_s2_row267_col71
  · simp [literalRow267, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk17.row267_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row267

def literalRow269 (j : Fin 222) : M := if j.val = 71 then 1073741826 else if j.val = 72 then 42 else if j.val = 73 then 1073743541 else 0

theorem literalSourceMatrix_row269 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨72, by decide⟩ : Fin 214)) = literalRow269 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 71
  · have hj : j = (⟨71, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow269]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 269 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d66_s2_row269_col71
  by_cases h1 : j.val = 72
  · have hj : j = (⟨72, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow269, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 269 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d67_s0_row269_col72
  by_cases h2 : j.val = 73
  · have hj : j = (⟨73, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow269, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 269 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk04.cell_d67_s2_row269_col73
  · simp [literalRow269, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk17.row269_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row269

end
end AspisV8R19.R804LiteralSourceRowsChunk17
