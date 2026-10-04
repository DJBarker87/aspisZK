import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748SchedulePrototype
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R778ActiveEntryPrototype
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748SchedulePrototype
noncomputable section
abbrev M := ZMod 2147483647

theorem active_entry_raw_column_133_row_code_257 :
    sourceChord (1073741824 : M)
      (direction (7 : M) (⟨127, by decide⟩ : Fin 255) (⟨2, by decide⟩ : Fin 3))
      (7 : M) (5 : M) (-5 : M) 257 = (83886080 : M) := by
  change sourceChord (1073741824 : M)
      (fun r => qPair (7 : M) (⟨127, by decide⟩ : Fin 255) (⟨2, by decide⟩ : Fin 3) r -
        qPair (7 : M) 0 (⟨2, by decide⟩ : Fin 3) r)
      (7 : M) (5 : M) (-5 : M) 257 = (83886080 : M)
  rw [sourceChord_difference]
  have hlow : sourceChord (1073741824 : M) (qPair (7 : M) 0 (⟨2, by decide⟩ : Fin 3))
      (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    exact sourceChord_low_pair_zero (1073741824 : M) (7 : M) (5 : M) (-5 : M) (7 : M)
      ⟨0, by decide⟩ ⟨2, by decide⟩ 257 (by decide)
  rw [hlow, sub_zero]
  have hq : qPair (7 : M) (⟨127, by decide⟩ : Fin 255) (⟨2, by decide⟩ : Fin 3) =
      (fun r => unitVector 511 r - (7 : M)^3 * unitVector 508 r) := by
    funext r
    simp [qPair]
  rw [hq, sourceChord_difference]
  rw [sourceChord_unit_odd_sourceGather (1073741824 : M) 255 257 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather (1073741824 : M) 254 257 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [gather255]
  norm_num [unitVector]

#print axioms active_entry_raw_column_133_row_code_257
end
end AspisV8R19.R778ActiveEntryPrototype
