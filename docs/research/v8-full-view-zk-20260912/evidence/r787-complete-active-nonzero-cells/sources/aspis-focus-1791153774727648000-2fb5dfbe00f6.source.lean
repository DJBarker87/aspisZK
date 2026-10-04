import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand03
import AspisV8R19.R748GatherExpand04
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk12
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand03
open AspisV8R19.R748GatherExpand04
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d87_s0_row351_col111 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 351 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 351 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 351
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 351 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 351 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 349 r - alphaSelected^1 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 349) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 351
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 174 351 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 351 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather174]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s0_row351_col111

theorem cell_d87_s2_row351_col112 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 351 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 351 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 351
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 351 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 351 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 351 r - alphaSelected^3 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 351) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 351
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 175 351 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 351 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather175]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s2_row351_col112

theorem cell_d87_s2_row353_col112 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 353 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 353
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 353 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 353 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 351 r - alphaSelected^3 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 351) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 353
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 175 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather175]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s2_row353_col112

theorem cell_d88_s0_row353_col113 :
    sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 353 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 353
  have hfun : (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 353 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 353 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 353 r - alphaSelected^1 * unitVector 352 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 353) (unitVector 352) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 353
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 176 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 176 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather176]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d88_s0_row353_col113

theorem cell_d88_s2_row353_col114 :
    sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 353 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 353
  have hfun : (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 353 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 353 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 355 r - alphaSelected^3 * unitVector 352 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 355) (unitVector 352) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 353
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 177 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 176 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather177]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d88_s2_row353_col114

theorem cell_d89_s2_row353_col116 :
    sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 353 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 353
  have hfun : (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 353 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 353 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 359 r - alphaSelected^3 * unitVector 356 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 359) (unitVector 356) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 353
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 179 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 178 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather179]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d89_s2_row353_col116

theorem cell_d91_s2_row353_col119 :
    sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 353 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 353
  have hfun : (fun r => qPair alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 353 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 353 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 367 r - alphaSelected^3 * unitVector 364 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 367) (unitVector 364) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 353
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 183 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 182 353 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather183]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d91_s2_row353_col119

theorem cell_d88_s0_row355_col113 :
    sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 355 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 355 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 355
  have hfun : (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 355 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 355 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 353 r - alphaSelected^1 * unitVector 352 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 353) (unitVector 352) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 355
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 176 355 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 176 355 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather176]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d88_s0_row355_col113

theorem cell_d88_s2_row355_col114 :
    sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 355 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 355 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 355
  have hfun : (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 355 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 355 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 355 r - alphaSelected^3 * unitVector 352 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 355) (unitVector 352) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 355
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 177 355 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 176 355 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather177]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d88_s2_row355_col114

theorem cell_d88_s2_row357_col114 :
    sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 357 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 357 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 357
  have hfun : (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 357 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 357 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 355 r - alphaSelected^3 * unitVector 352 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 355) (unitVector 352) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 357
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 177 357 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 176 357 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather177]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d88_s2_row357_col114

theorem cell_d89_s0_row357_col115 :
    sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 357 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 357 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 357
  have hfun : (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 357 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 357 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 357 r - alphaSelected^1 * unitVector 356 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 357) (unitVector 356) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 357
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 178 357 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 178 357 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather178]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d89_s0_row357_col115

theorem cell_d89_s2_row357_col116 :
    sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 357 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 357 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 357
  have hfun : (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 357 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 357 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 359 r - alphaSelected^3 * unitVector 356 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 359) (unitVector 356) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 357
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 179 357 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 178 357 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather179]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d89_s2_row357_col116

theorem cell_d89_s0_row359_col115 :
    sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 359 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 359 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 359
  have hfun : (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 359 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 359 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 357 r - alphaSelected^1 * unitVector 356 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 357) (unitVector 356) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 359
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 178 359 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 178 359 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather178]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d89_s0_row359_col115

theorem cell_d89_s2_row359_col116 :
    sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 359 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 359 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 359
  have hfun : (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 359 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 359 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 359 r - alphaSelected^3 * unitVector 356 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 359) (unitVector 356) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 359
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 179 359 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 178 359 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather179]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d89_s2_row359_col116

theorem cell_d89_s2_row361_col116 :
    sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 361 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 361 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 361
  have hfun : (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 361 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 361 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 359 r - alphaSelected^3 * unitVector 356 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 359) (unitVector 356) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 361
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 179 361 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 178 361 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather179]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d89_s2_row361_col116

theorem cell_d90_s0_row361_col117 :
    sourceChord halfSelected (direction alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 361 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 361 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 361
  have hfun : (fun r => qPair alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 361 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 361 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨90, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 361 r - alphaSelected^1 * unitVector 360 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 361) (unitVector 360) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 361
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 180 361 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 180 361 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather180]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d90_s0_row361_col117
end
end AspisV8R19.R799ActiveSourceCellsChunk12
