import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk24
import AspisV8R19.R799ActiveSourceCellsChunk25
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk44
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk44
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow942 (j : Fin 222) : M := if j.val = 176 then 2147483612 else if j.val = 177 then 2147483409 else 0

theorem literalSourceMatrix_row942 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨177, by decide⟩ : Fin 214)) = literalRow942 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 176
  · have hj : j = (⟨176, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow942]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 942 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s0_row942_col176
  by_cases h1 : j.val = 177
  · have hj : j = (⟨177, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow942, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 942 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s1_row942_col177
  · simp [literalRow942, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk44.row942_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row942

def literalRow944 (j : Fin 222) : M := if j.val = 176 then 1342177280 else if j.val = 177 then 1342177280 else if j.val = 178 then 1073741772 else if j.val = 179 then 536870913 else if j.val = 182 then 1342177280 else 0

theorem literalSourceMatrix_row944 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨178, by decide⟩ : Fin 214)) = literalRow944 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 176
  · have hj : j = (⟨176, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow944]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 944 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s0_row944_col176
  by_cases h1 : j.val = 177
  · have hj : j = (⟨177, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow944, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 944 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s1_row944_col177
  by_cases h2 : j.val = 178
  · have hj : j = (⟨178, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow944, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨236, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 944 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d236_s0_row944_col178
  by_cases h3 : j.val = 179
  · have hj : j = (⟨179, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow944, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨237, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 944 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d237_s0_row944_col179
  by_cases h4 : j.val = 182
  · have hj : j = (⟨182, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow944, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨239, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 944 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d239_s1_row944_col182
  · simp [literalRow944, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk44.row944_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row944

def literalRow948 (j : Fin 222) : M := if j.val = 178 then 1073741826 else if j.val = 179 then 1073741772 else 0

theorem literalSourceMatrix_row948 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨179, by decide⟩ : Fin 214)) = literalRow948 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 178
  · have hj : j = (⟨178, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow948]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨236, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 948 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d236_s0_row948_col178
  by_cases h1 : j.val = 179
  · have hj : j = (⟨179, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow948, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨237, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 948 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d237_s0_row948_col179
  · simp [literalRow948, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk44.row948_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row948

def literalRow952 (j : Fin 222) : M := if j.val = 179 then 536870913 else if j.val = 180 then 1073741772 else if j.val = 181 then 1073741483 else if j.val = 182 then 536870913 else 0

theorem literalSourceMatrix_row952 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨180, by decide⟩ : Fin 214)) = literalRow952 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 179
  · have hj : j = (⟨179, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow952]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨237, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 952 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d237_s0_row952_col179
  by_cases h1 : j.val = 180
  · have hj : j = (⟨180, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow952, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨238, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 952 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d238_s0_row952_col180
  by_cases h2 : j.val = 181
  · have hj : j = (⟨181, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow952, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨238, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 952 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d238_s1_row952_col181
  by_cases h3 : j.val = 182
  · have hj : j = (⟨182, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow952, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨239, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 952 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d239_s1_row952_col182
  · simp [literalRow952, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk44.row952_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row952

end
end AspisV8R19.R804LiteralSourceRowsChunk44
