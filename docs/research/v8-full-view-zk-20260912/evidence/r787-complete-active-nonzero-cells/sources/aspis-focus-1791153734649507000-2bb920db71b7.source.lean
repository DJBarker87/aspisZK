import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherExpand03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk06
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherExpand03
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d71_s2_row281_col81 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 281 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 281
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 281 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 281 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 287 r - alphaSelected^3 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 287) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 281
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 143 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather143]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s2_row281_col81

theorem cell_d70_s0_row283_col78 :
    sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 283 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 283 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 283
  have hfun : (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 283 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 283 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 281 r - alphaSelected^1 * unitVector 280 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 281) (unitVector 280) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 283
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 140 283 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 140 283 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather140]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d70_s0_row283_col78

theorem cell_d70_s2_row283_col79 :
    sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 283 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 283 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 283
  have hfun : (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 283 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 283 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 283 r - alphaSelected^3 * unitVector 280 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 283) (unitVector 280) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 283
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 141 283 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 140 283 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather141]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d70_s2_row283_col79

theorem cell_d70_s2_row285_col79 :
    sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 285 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 285 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 285
  have hfun : (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 285 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 285 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 283 r - alphaSelected^3 * unitVector 280 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 283) (unitVector 280) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 285
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 141 285 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 140 285 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather141]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d70_s2_row285_col79

theorem cell_d71_s0_row285_col80 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 285 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 285 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 285
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 285 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 285 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 285 r - alphaSelected^1 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 285) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 285
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 142 285 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 285 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather142]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s0_row285_col80

theorem cell_d71_s2_row285_col81 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 285 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 285 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 285
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 285 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 285 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 287 r - alphaSelected^3 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 287) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 285
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 143 285 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 285 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather143]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s2_row285_col81

theorem cell_d71_s0_row287_col80 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 287 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 287 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 287
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 287 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 287 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 285 r - alphaSelected^1 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 285) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 287
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 142 287 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 287 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather142]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s0_row287_col80

theorem cell_d71_s2_row287_col81 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 287 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 287 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 287
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 287 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 287 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 287 r - alphaSelected^3 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 287) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 287
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 143 287 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 287 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather143]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s2_row287_col81

theorem cell_d71_s2_row289_col81 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 289 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 289
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 289 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 289 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 287 r - alphaSelected^3 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 287) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 289
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 143 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather143]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s2_row289_col81

theorem cell_d72_s0_row289_col82 :
    sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 289 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 289
  have hfun : (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 289 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 289 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 289 r - alphaSelected^1 * unitVector 288 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 289) (unitVector 288) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 289
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 144 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 144 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather144]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d72_s0_row289_col82

theorem cell_d72_s2_row289_col83 :
    sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 289 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 289
  have hfun : (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 289 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 289 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 291 r - alphaSelected^3 * unitVector 288 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 291) (unitVector 288) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 289
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 145 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 144 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather145]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d72_s2_row289_col83

theorem cell_d73_s2_row289_col85 :
    sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 289 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 289
  have hfun : (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 289 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 289 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 295 r - alphaSelected^3 * unitVector 292 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 295) (unitVector 292) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 289
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 147 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 146 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather147]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d73_s2_row289_col85

theorem cell_d75_s2_row289_col89 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 289 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 289
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 289 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 289 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 303 r - alphaSelected^3 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 303) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 289
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 151 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather151]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s2_row289_col89

theorem cell_d79_s2_row289_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 289 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 289 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 289
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 289 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 289 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 289
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 289 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row289_col96

theorem cell_d72_s0_row291_col82 :
    sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 291 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 291 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 291
  have hfun : (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 291 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 291 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨72, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 289 r - alphaSelected^1 * unitVector 288 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 289) (unitVector 288) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 291
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 144 291 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 144 291 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather144]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d72_s0_row291_col82

theorem cell_d72_s2_row291_col83 :
    sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 291 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 291 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 291
  have hfun : (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 291 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 291 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 291 r - alphaSelected^3 * unitVector 288 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 291) (unitVector 288) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 291
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 145 291 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 144 291 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather145]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d72_s2_row291_col83
end
end AspisV8R19.R799ActiveSourceCellsChunk06
