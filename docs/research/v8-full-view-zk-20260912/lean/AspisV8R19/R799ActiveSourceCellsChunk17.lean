import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand04
import AspisV8R19.R748GatherNested03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk17
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand04
open AspisV8R19.R748GatherNested03
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d159_s0_row638_col139 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 638 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 638 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 638
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 638 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 638 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 637 r - alphaSelected^1 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 637) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 638
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 318 638 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 638 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather318]
  rw [gather318]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s0_row638_col139

theorem cell_d159_s1_row638_col140 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 638 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 638 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 638
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 638 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 638 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 638 r - alphaSelected^2 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 638) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 638
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 319 638 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 638 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather319]
  rw [gather318]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s1_row638_col140

theorem cell_d159_s2_row638_col141 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 638 = (1073740106 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 638 = (1073740106 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 638
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 638 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 638 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 639 r - alphaSelected^3 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 639) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 638
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 319 638 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 638 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather319]
  rw [gather318]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s2_row638_col141

theorem cell_d159_s0_row639_col139 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 639 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 639 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 639
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 639 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 639 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 637 r - alphaSelected^1 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 637) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 639
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 318 639 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 639 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather318]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s0_row639_col139

theorem cell_d159_s1_row639_col140 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 639 = (2147483642 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 639 = (2147483642 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 639
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 639 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 639 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 638 r - alphaSelected^2 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 638) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 639
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 319 639 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 639 (by decide) (7 : M) (5 : M) (-5 : M)]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s1_row639_col140

theorem cell_d159_s2_row639_col141 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 639 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 639 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 639
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 639 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 639 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 639 r - alphaSelected^3 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 639) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 639
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 319 639 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 639 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather319]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s2_row639_col141

theorem cell_d188_s2_row755_col142 :
    sourceChord halfSelected (direction alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 755 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 755 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 755
  have hfun : (fun r => qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 755 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 755 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 755 r - alphaSelected^3 * unitVector 752 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 755) (unitVector 752) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 755
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 377 755 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 376 755 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather377]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d188_s2_row755_col142

theorem cell_d188_s2_row757_col142 :
    sourceChord halfSelected (direction alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 757 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 757 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 757
  have hfun : (fun r => qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 757 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 757 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨188, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 755 r - alphaSelected^3 * unitVector 752 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 755) (unitVector 752) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 757
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 377 757 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 376 757 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather377]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d188_s2_row757_col142

theorem cell_d189_s0_row757_col143 :
    sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 757 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 757 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 757
  have hfun : (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 757 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 757 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 757 r - alphaSelected^1 * unitVector 756 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 757) (unitVector 756) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 757
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 378 757 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 378 757 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather378]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d189_s0_row757_col143

theorem cell_d189_s2_row757_col144 :
    sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 757 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 757 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 757
  have hfun : (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 757 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 757 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 759 r - alphaSelected^3 * unitVector 756 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 759) (unitVector 756) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 757
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 379 757 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 378 757 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather379]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d189_s2_row757_col144

theorem cell_d189_s0_row759_col143 :
    sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 759 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 759 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 759
  have hfun : (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 759 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 759 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨189, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 757 r - alphaSelected^1 * unitVector 756 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 757) (unitVector 756) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 759
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 378 759 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 378 759 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather378]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d189_s0_row759_col143

theorem cell_d189_s2_row759_col144 :
    sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 759 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 759 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 759
  have hfun : (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 759 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 759 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 759 r - alphaSelected^3 * unitVector 756 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 759) (unitVector 756) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 759
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 379 759 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 378 759 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather379]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d189_s2_row759_col144

theorem cell_d189_s2_row761_col144 :
    sourceChord halfSelected (direction alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 761 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 761 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 761
  have hfun : (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 761 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 761 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨189, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 759 r - alphaSelected^3 * unitVector 756 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 759) (unitVector 756) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 761
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 379 761 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 378 761 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather379]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d189_s2_row761_col144

theorem cell_d190_s0_row761_col145 :
    sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 761 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 761 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 761
  have hfun : (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 761 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 761 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 761 r - alphaSelected^1 * unitVector 760 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 761) (unitVector 760) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 761
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 380 761 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 380 761 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather380]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d190_s0_row761_col145

theorem cell_d190_s2_row761_col146 :
    sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 761 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 761 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 761
  have hfun : (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 761 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 761 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨190, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 763 r - alphaSelected^3 * unitVector 760 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 763) (unitVector 760) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 761
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 381 761 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 380 761 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather381]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d190_s2_row761_col146

theorem cell_d190_s0_row763_col145 :
    sourceChord halfSelected (direction alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 763 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 763 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 763
  have hfun : (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 763 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 763 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨190, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 761 r - alphaSelected^1 * unitVector 760 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 761) (unitVector 760) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 763
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 380 763 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 380 763 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather380]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d190_s0_row763_col145
end
end AspisV8R19.R799ActiveSourceCellsChunk17
