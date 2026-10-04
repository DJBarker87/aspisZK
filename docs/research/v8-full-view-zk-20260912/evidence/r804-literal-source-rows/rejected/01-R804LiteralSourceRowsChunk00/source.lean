import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk00
import AspisV8R19.R797ActiveSourceCellsPreflight
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk00
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk00
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow116 (j : Fin 222) : M := if j.val = 0 then 1073741826 else if j.val = 1 then 1073741772 else if j.val = 2 then 1073741483 else 0

theorem literalSourceMatrix_row116 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨1, by decide⟩ : Fin 214)) = literalRow116 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 0
  · have hj : j = (⟨0, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow116]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 116 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d28_s1_row116_col0
  by_cases h1 : j.val = 1
  · have hj : j = (⟨1, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow116, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 116 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsPreflight.cell_d29_s0_row116
  by_cases h2 : j.val = 2
  · have hj : j = (⟨2, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow116, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 116 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d29_s1_row116_col2
  · simp [literalRow116, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk00.row116_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    simp only [List.mem_cons, List.not_mem_nil]
    omega
#print axioms literalSourceMatrix_row116

def literalRow118 (j : Fin 222) : M := if j.val = 1 then 2147483612 else if j.val = 2 then 2147483409 else 0

theorem literalSourceMatrix_row118 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨2, by decide⟩ : Fin 214)) = literalRow118 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 1
  · have hj : j = (⟨1, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow118]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 118 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d29_s0_row118_col1
  by_cases h1 : j.val = 2
  · have hj : j = (⟨2, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow118, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 118 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d29_s1_row118_col2
  · simp [literalRow118, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk00.row118_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    simp only [List.mem_cons, List.not_mem_nil]
    omega
#print axioms literalSourceMatrix_row118

def literalRow120 (j : Fin 222) : M := if j.val = 1 then 536870913 else if j.val = 2 then 536870913 else if j.val = 3 then 1073741772 else if j.val = 4 then 1073741483 else if j.val = 5 then 536870913 else if j.val = 6 then 536870913 else 0

theorem literalSourceMatrix_row120 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨3, by decide⟩ : Fin 214)) = literalRow120 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 1
  · have hj : j = (⟨1, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow120]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 120 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d29_s0_row120_col1
  by_cases h1 : j.val = 2
  · have hj : j = (⟨2, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow120, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 120 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d29_s1_row120_col2
  by_cases h2 : j.val = 3
  · have hj : j = (⟨3, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow120, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨30, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 120 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d30_s0_row120_col3
  by_cases h3 : j.val = 4
  · have hj : j = (⟨4, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow120, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨30, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 120 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d30_s1_row120_col4
  by_cases h4 : j.val = 5
  · have hj : j = (⟨5, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow120, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 120 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d31_s0_row120_col5
  by_cases h5 : j.val = 6
  · have hj : j = (⟨6, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow120, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 120 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d31_s1_row120_col6
  · simp [literalRow120, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk00.row120_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    simp only [List.mem_cons, List.not_mem_nil]
    omega
#print axioms literalSourceMatrix_row120

def literalRow122 (j : Fin 222) : M := if j.val = 3 then 2147483612 else if j.val = 4 then 2147483409 else 0

theorem literalSourceMatrix_row122 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨4, by decide⟩ : Fin 214)) = literalRow122 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 3
  · have hj : j = (⟨3, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow122]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨30, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 122 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d30_s0_row122_col3
  by_cases h1 : j.val = 4
  · have hj : j = (⟨4, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow122, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨30, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 122 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d30_s1_row122_col4
  · simp [literalRow122, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk00.row122_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    simp only [List.mem_cons, List.not_mem_nil]
    omega
#print axioms literalSourceMatrix_row122

end
end AspisV8R19.R804LiteralSourceRowsChunk00
