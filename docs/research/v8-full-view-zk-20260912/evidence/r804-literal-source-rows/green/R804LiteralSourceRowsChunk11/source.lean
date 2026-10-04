import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk08
import AspisV8R19.R797ActiveSourceCellsChunk09
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk11
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk11
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow212 (j : Fin 222) : M := if j.val = 43 then 1073741826 else if j.val = 44 then 1073741826 else if j.val = 45 then 1073741772 else if j.val = 46 then 1073741483 else 0

theorem literalSourceMatrix_row212 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨45, by decide⟩ : Fin 214)) = literalRow212 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 43
  · have hj : j = (⟨43, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow212]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨52, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 212 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d52_s0_row212_col43
  by_cases h1 : j.val = 44
  · have hj : j = (⟨44, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow212, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨52, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 212 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d52_s1_row212_col44
  by_cases h2 : j.val = 45
  · have hj : j = (⟨45, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow212, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 212 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d53_s0_row212_col45
  by_cases h3 : j.val = 46
  · have hj : j = (⟨46, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow212, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 212 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d53_s1_row212_col46
  · simp [literalRow212, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk11.row212_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row212

def literalRow214 (j : Fin 222) : M := if j.val = 45 then 2147483612 else if j.val = 46 then 2147483409 else 0

theorem literalSourceMatrix_row214 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨46, by decide⟩ : Fin 214)) = literalRow214 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 45
  · have hj : j = (⟨45, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow214]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 214 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d53_s0_row214_col45
  by_cases h1 : j.val = 46
  · have hj : j = (⟨46, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow214, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 214 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d53_s1_row214_col46
  · simp [literalRow214, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk11.row214_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row214

def literalRow216 (j : Fin 222) : M := if j.val = 45 then 536870913 else if j.val = 46 then 536870913 else if j.val = 47 then 1073741772 else if j.val = 48 then 1073741483 else if j.val = 49 then 536870913 else if j.val = 50 then 536870913 else 0

theorem literalSourceMatrix_row216 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨47, by decide⟩ : Fin 214)) = literalRow216 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 45
  · have hj : j = (⟨45, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow216]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 216 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d53_s0_row216_col45
  by_cases h1 : j.val = 46
  · have hj : j = (⟨46, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow216, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 216 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d53_s1_row216_col46
  by_cases h2 : j.val = 47
  · have hj : j = (⟨47, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow216, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨54, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 216 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d54_s0_row216_col47
  by_cases h3 : j.val = 48
  · have hj : j = (⟨48, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow216, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨54, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 216 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d54_s1_row216_col48
  by_cases h4 : j.val = 49
  · have hj : j = (⟨49, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow216, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 216 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d55_s0_row216_col49
  by_cases h5 : j.val = 50
  · have hj : j = (⟨50, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow216, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 216 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d55_s1_row216_col50
  · simp [literalRow216, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk11.row216_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row216

def literalRow218 (j : Fin 222) : M := if j.val = 47 then 2147483612 else if j.val = 48 then 2147483409 else 0

theorem literalSourceMatrix_row218 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨48, by decide⟩ : Fin 214)) = literalRow218 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 47
  · have hj : j = (⟨47, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow218]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨54, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 218 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d54_s0_row218_col47
  by_cases h1 : j.val = 48
  · have hj : j = (⟨48, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow218, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨54, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 218 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d54_s1_row218_col48
  · simp [literalRow218, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk11.row218_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row218

end
end AspisV8R19.R804LiteralSourceRowsChunk11
