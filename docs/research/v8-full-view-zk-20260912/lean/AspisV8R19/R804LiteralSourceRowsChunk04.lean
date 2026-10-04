import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk03
import AspisV8R19.R797ActiveSourceCellsChunk04
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk04
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk04
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow148 (j : Fin 222) : M := if j.val = 15 then 1073741826 else if j.val = 16 then 1073741826 else if j.val = 17 then 1073741772 else if j.val = 18 then 1073741483 else 0

theorem literalSourceMatrix_row148 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨17, by decide⟩ : Fin 214)) = literalRow148 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 15
  · have hj : j = (⟨15, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow148]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨36, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 148 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d36_s0_row148_col15
  by_cases h1 : j.val = 16
  · have hj : j = (⟨16, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow148, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨36, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 148 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d36_s1_row148_col16
  by_cases h2 : j.val = 17
  · have hj : j = (⟨17, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow148, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 148 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s0_row148_col17
  by_cases h3 : j.val = 18
  · have hj : j = (⟨18, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow148, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 148 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s1_row148_col18
  · simp [literalRow148, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk04.row148_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row148

def literalRow150 (j : Fin 222) : M := if j.val = 17 then 2147483612 else if j.val = 18 then 2147483409 else 0

theorem literalSourceMatrix_row150 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨18, by decide⟩ : Fin 214)) = literalRow150 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 17
  · have hj : j = (⟨17, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow150]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 150 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s0_row150_col17
  by_cases h1 : j.val = 18
  · have hj : j = (⟨18, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow150, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 150 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s1_row150_col18
  · simp [literalRow150, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk04.row150_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row150

def literalRow152 (j : Fin 222) : M := if j.val = 17 then 536870913 else if j.val = 18 then 536870913 else if j.val = 19 then 1073741772 else if j.val = 20 then 1073741483 else if j.val = 21 then 536870913 else if j.val = 22 then 536870913 else 0

theorem literalSourceMatrix_row152 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨19, by decide⟩ : Fin 214)) = literalRow152 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 17
  · have hj : j = (⟨17, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow152]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 152 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s0_row152_col17
  by_cases h1 : j.val = 18
  · have hj : j = (⟨18, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow152, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨37, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 152 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d37_s1_row152_col18
  by_cases h2 : j.val = 19
  · have hj : j = (⟨19, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow152, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨38, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 152 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk03.cell_d38_s0_row152_col19
  by_cases h3 : j.val = 20
  · have hj : j = (⟨20, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow152, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨38, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 152 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d38_s1_row152_col20
  by_cases h4 : j.val = 21
  · have hj : j = (⟨21, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow152, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 152 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s0_row152_col21
  by_cases h5 : j.val = 22
  · have hj : j = (⟨22, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow152, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 152 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d39_s1_row152_col22
  · simp [literalRow152, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk04.row152_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row152

def literalRow154 (j : Fin 222) : M := if j.val = 19 then 2147483612 else if j.val = 20 then 2147483409 else 0

theorem literalSourceMatrix_row154 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨20, by decide⟩ : Fin 214)) = literalRow154 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 19
  · have hj : j = (⟨19, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow154]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨38, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 154 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d38_s0_row154_col19
  by_cases h1 : j.val = 20
  · have hj : j = (⟨20, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow154, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨38, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 154 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk04.cell_d38_s1_row154_col20
  · simp [literalRow154, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk04.row154_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row154

end
end AspisV8R19.R804LiteralSourceRowsChunk04
