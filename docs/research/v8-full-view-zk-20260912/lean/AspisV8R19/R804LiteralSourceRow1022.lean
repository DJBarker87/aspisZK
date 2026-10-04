import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R778ActiveEntryPrototype
import AspisV8R19.R748JointWitnessPointEntry
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRow1022
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R800SelectedSupportPrototype
noncomputable section
abbrev M := ZMod 2147483647
def literalRow1022 (j : Fin 222) : M := if j.val = 212 then 1073741826 else 0
theorem literalSourceMatrix_row1022 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected kappaSelected tauSelected z)
      (activePosition (⟨213, by decide⟩ : Fin 214)) = literalRow1022 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h : j.val = 212
  · have hj : j = (⟨212, by decide⟩ : Fin 222) := Fin.ext h
    subst j
    simp [literalRow1022]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩)) (7:M) (5:M) (-5:M) 1022 = (1073741826:M)
    exact AspisV8R19.R778ActiveEntryPrototype.active_entry_raw_column_212_row_code_1022
  · simp [literalRow1022,h]
    rw [literalSourceMatrix_active_entry]
    exact AspisV8R19.R800SelectedSupportPrototype.row1022_source_zero halfSelected alphaSelected (7:M) (5:M) (-5:M) j (by simpa using h)
#print axioms literalSourceMatrix_row1022
end
end AspisV8R19.R804LiteralSourceRow1022
