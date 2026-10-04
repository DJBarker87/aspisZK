import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748SchedulePrototype
import AspisV8R19.R748GatherExpand07
import AspisV8R19.R748GatherNested04
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R778ActiveEntryPrototype
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748SchedulePrototype
open AspisV8R19.R748GatherExpand07
open AspisV8R19.R748GatherNested04
noncomputable section
abbrev M := ZMod 2147483647
def d127 : Fin 255 := ⟨127, by decide⟩
def d254 : Fin 255 := ⟨254, by decide⟩
def s2 : Fin 3 := ⟨2, by decide⟩

def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem active_entry_raw_column_133_row_code_257 :
    sourceChord halfSelected (direction alphaSelected d127 s2)
      (7 : M) (5 : M) (-5 : M) 257 = (83886080 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected d127 s2 r - qPair alphaSelected 0 s2 r)
      (7 : M) (5 : M) (-5 : M) 257 = (83886080 : M)
  have hdiff := sourceChord_difference halfSelected (qPair alphaSelected d127 s2)
      (qPair alphaSelected 0 s2) (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected d127 s2 r - qPair alphaSelected 0 s2 r) =
      (fun r => qPair alphaSelected d127 s2 r - (1 : M) * qPair alphaSelected 0 s2 r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 s2)
      (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected, s2] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ s2 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected d127 s2 =
      (fun r => unitVector 511 r - alphaSelected^3 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected, d127, s2]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 511) (unitVector 508)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 255 257 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 254 257 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [R748SchedulePrototype.gather255]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide

/-- The raw R724 active row slot 213 is labeled `active_chord_1022`; its
selected raw column 212 is the `(254,3)` direction (Lean `(254,2)`). -/
theorem active_entry_raw_column_212_row_code_1022 :
    sourceChord halfSelected (direction alphaSelected d254 s2)
      (7 : M) (5 : M) (-5 : M) 1022 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected d254 s2 r - qPair alphaSelected 0 s2 r)
      (7 : M) (5 : M) (-5 : M) 1022 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected (qPair alphaSelected d254 s2)
      (qPair alphaSelected 0 s2) (7 : M) (5 : M) (-5 : M) (1 : M) 1022
  have hfun : (fun r => qPair alphaSelected d254 s2 r - qPair alphaSelected 0 s2 r) =
      (fun r => qPair alphaSelected d254 s2 r - (1 : M) * qPair alphaSelected 0 s2 r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 s2)
      (7 : M) (5 : M) (-5 : M) 1022 = 0 := by
    simpa [alphaSelected, s2] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ s2 1022 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected d254 s2 =
      (fun r => unitVector 1019 r - alphaSelected^3 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected, d254, s2]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1019) (unitVector 1016)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1022
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 509 1022 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1022 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [R748GatherNested04.gatherGather509, R748GatherExpand07.gather508]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide

#print axioms active_entry_raw_column_133_row_code_257
#print axioms active_entry_raw_column_212_row_code_1022
end
end AspisV8R19.R778ActiveEntryPrototype
