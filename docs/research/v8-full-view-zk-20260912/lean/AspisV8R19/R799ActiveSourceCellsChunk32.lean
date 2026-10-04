import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand07
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk32
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand07
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d254_s0_row1017_col211 :
    sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1017 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1017
  have hfun : (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1017 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1017 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1017 r - alphaSelected^1 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1017) (unitVector 1016) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1017
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 508 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather508]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d254_s0_row1017_col211

theorem cell_d254_s2_row1017_col212 :
    sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1017 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1017
  have hfun : (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1017 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1017 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1019 r - alphaSelected^3 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1019) (unitVector 1016) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1017
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 509 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather509]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d254_s2_row1017_col212

theorem cell_d254_s1_row1017_col213 :
    sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (245 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1017 = (245 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1017
  have hfun : (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1017 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 1017 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 1018 r - alphaSelected^2 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1018) (unitVector 1016) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 1017
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 509 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d254_s1_row1017_col213

theorem cell_d254_s0_row1019_col211 :
    sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1019 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1019 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1019
  have hfun : (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1019 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1019 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨254, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1017 r - alphaSelected^1 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1017) (unitVector 1016) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1019
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 508 1019 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1019 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather508]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d254_s0_row1019_col211

theorem cell_d254_s2_row1019_col212 :
    sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1019 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1019 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1019
  have hfun : (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1019 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1019 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1019 r - alphaSelected^3 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1019) (unitVector 1016) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1019
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 509 1019 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1019 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather509]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d254_s2_row1019_col212

theorem cell_d254_s1_row1019_col213 :
    sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1019 = (2147483642 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1019 = (2147483642 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1019
  have hfun : (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1019 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 1019 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨254, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 1018 r - alphaSelected^2 * unitVector 1016 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1018) (unitVector 1016) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 1019
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 509 1019 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 508 1019 (by decide) (7 : M) (5 : M) (-5 : M)]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d254_s1_row1019_col213
end
end AspisV8R19.R799ActiveSourceCellsChunk32
