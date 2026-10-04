import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk28
import AspisV8R19.R799ActiveSourceCellsChunk29
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk49
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk49
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow988 (j : Fin 222) : M := if j.val = 195 then 1073741826 else if j.val = 196 then 1073741826 else if j.val = 197 then 1073741772 else if j.val = 198 then 1073741483 else 0

theorem literalSourceMatrix_row988 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨197, by decide⟩ : Fin 214)) = literalRow988 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 195
  · have hj : j = (⟨195, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow988]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨246, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 988 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d246_s0_row988_col195
  by_cases h1 : j.val = 196
  · have hj : j = (⟨196, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow988, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨246, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 988 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d246_s1_row988_col196
  by_cases h2 : j.val = 197
  · have hj : j = (⟨197, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow988, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 988 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d247_s0_row988_col197
  by_cases h3 : j.val = 198
  · have hj : j = (⟨198, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow988, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 988 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d247_s1_row988_col198
  · simp [literalRow988, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk49.row988_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row988

def literalRow990 (j : Fin 222) : M := if j.val = 197 then 2147483612 else if j.val = 198 then 2147483409 else 0

theorem literalSourceMatrix_row990 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨198, by decide⟩ : Fin 214)) = literalRow990 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 197
  · have hj : j = (⟨197, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow990]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 990 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d247_s0_row990_col197
  by_cases h1 : j.val = 198
  · have hj : j = (⟨198, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow990, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 990 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d247_s1_row990_col198
  · simp [literalRow990, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk49.row990_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row990

def literalRow992 (j : Fin 222) : M := if j.val = 197 then 671088640 else if j.val = 198 then 671088640 else if j.val = 199 then 1073741772 else if j.val = 200 then 1073741483 else if j.val = 201 then 536870913 else if j.val = 202 then 536870913 else if j.val = 205 then 1342177280 else if j.val = 206 then 1342177280 else 0

theorem literalSourceMatrix_row992 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨199, by decide⟩ : Fin 214)) = literalRow992 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 197
  · have hj : j = (⟨197, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow992]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d247_s0_row992_col197
  by_cases h1 : j.val = 198
  · have hj : j = (⟨198, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow992, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d247_s1_row992_col198
  by_cases h2 : j.val = 199
  · have hj : j = (⟨199, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow992, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨248, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d248_s0_row992_col199
  by_cases h3 : j.val = 200
  · have hj : j = (⟨200, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow992, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨248, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d248_s1_row992_col200
  by_cases h4 : j.val = 201
  · have hj : j = (⟨201, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow992, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d249_s0_row992_col201
  by_cases h5 : j.val = 202
  · have hj : j = (⟨202, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow992, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d249_s1_row992_col202
  by_cases h6 : j.val = 205
  · have hj : j = (⟨205, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow992, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d251_s0_row992_col205
  by_cases h7 : j.val = 206
  · have hj : j = (⟨206, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow992, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 992 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d251_s1_row992_col206
  · simp [literalRow992, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk49.row992_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
    · exact h7 hbad
#print axioms literalSourceMatrix_row992

def literalRow994 (j : Fin 222) : M := if j.val = 199 then 2147483612 else if j.val = 200 then 2147483409 else 0

theorem literalSourceMatrix_row994 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨200, by decide⟩ : Fin 214)) = literalRow994 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 199
  · have hj : j = (⟨199, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow994]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨248, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 994 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d248_s0_row994_col199
  by_cases h1 : j.val = 200
  · have hj : j = (⟨200, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow994, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨248, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 994 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d248_s1_row994_col200
  · simp [literalRow994, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk49.row994_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row994

end
end AspisV8R19.R804LiteralSourceRowsChunk49
