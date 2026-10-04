import AspisV8R19.R778ActiveEntryPrototype

set_option autoImplicit false
namespace AspisV8R19.R786ActiveZeroPrototype
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R778ActiveEntryPrototype
noncomputable section

theorem active_entry_raw_column_133_row_code_114 :
    sourceChord halfSelected (direction alphaSelected d127 s2)
      (7 : M) (5 : M) (-5 : M) 114 = 0 := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected d127 s2 r - qPair alphaSelected 0 s2 r)
      (7 : M) (5 : M) (-5 : M) 114 = 0
  have hdiff := sourceChord_difference halfSelected (qPair alphaSelected d127 s2)
      (qPair alphaSelected 0 s2) (7 : M) (5 : M) (-5 : M) (1 : M) 114
  have hfun : (fun r => qPair alphaSelected d127 s2 r - qPair alphaSelected 0 s2 r) =
      (fun r => qPair alphaSelected d127 s2 r - (1 : M) * qPair alphaSelected 0 s2 r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 s2)
      (7 : M) (5 : M) (-5 : M) 114 = 0 := by
    simpa [alphaSelected, s2] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ s2 114 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected d127 s2 =
      (fun r => unitVector 511 r - alphaSelected^3 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected, d127, s2]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 511) (unitVector 508)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 114
  rw [hdiff2]
  have hodd : ¬oddUnitSupport 255 114 := by decide
  have heven : ¬evenUnitSupport 254 114 := by decide
  rw [sourceChord_odd_zero halfSelected 255 114 (by decide) hodd
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_even_zero halfSelected 254 114 (by decide) heven
      (7 : M) (5 : M) (-5 : M)]
  simp

#print axioms active_entry_raw_column_133_row_code_114
end
end AspisV8R19.R786ActiveZeroPrototype
