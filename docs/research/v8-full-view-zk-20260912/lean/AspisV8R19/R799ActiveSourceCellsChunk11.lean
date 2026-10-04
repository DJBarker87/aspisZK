import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk11
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand03
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d84_s0_row339_col105 :
    sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 339 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 339 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 339
  have hfun : (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 339 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 339 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨84, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 337 r - alphaSelected^1 * unitVector 336 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 337) (unitVector 336) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 339
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 168 339 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 168 339 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather168]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d84_s0_row339_col105

theorem cell_d84_s2_row339_col106 :
    sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 339 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 339 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 339
  have hfun : (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 339 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 339 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 339 r - alphaSelected^3 * unitVector 336 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 339) (unitVector 336) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 339
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 169 339 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 168 339 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather169]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d84_s2_row339_col106

theorem cell_d84_s2_row341_col106 :
    sourceChord halfSelected (direction alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 341 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 341 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 341
  have hfun : (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 341 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 341 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨84, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 339 r - alphaSelected^3 * unitVector 336 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 339) (unitVector 336) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 341
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 169 341 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 168 341 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather169]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d84_s2_row341_col106

theorem cell_d85_s0_row341_col107 :
    sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 341 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 341 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 341
  have hfun : (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 341 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 341 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 341 r - alphaSelected^1 * unitVector 340 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 341) (unitVector 340) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 341
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 170 341 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 170 341 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather170]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d85_s0_row341_col107

theorem cell_d85_s2_row341_col108 :
    sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 341 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 341 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 341
  have hfun : (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 341 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 341 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 343 r - alphaSelected^3 * unitVector 340 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 343) (unitVector 340) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 341
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 171 341 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 170 341 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather171]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d85_s2_row341_col108

theorem cell_d85_s0_row343_col107 :
    sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 343 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 343 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 343
  have hfun : (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 343 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 343 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨85, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 341 r - alphaSelected^1 * unitVector 340 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 341) (unitVector 340) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 343
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 170 343 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 170 343 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather170]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d85_s0_row343_col107

theorem cell_d85_s2_row343_col108 :
    sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 343 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 343 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 343
  have hfun : (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 343 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 343 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 343 r - alphaSelected^3 * unitVector 340 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 343) (unitVector 340) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 343
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 171 343 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 170 343 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather171]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d85_s2_row343_col108

theorem cell_d85_s2_row345_col108 :
    sourceChord halfSelected (direction alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 345 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 345
  have hfun : (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 345 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 345 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨85, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 343 r - alphaSelected^3 * unitVector 340 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 343) (unitVector 340) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 345
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 171 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 170 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather171]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d85_s2_row345_col108

theorem cell_d86_s0_row345_col109 :
    sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 345 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 345
  have hfun : (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 345 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 345 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 345 r - alphaSelected^1 * unitVector 344 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 345) (unitVector 344) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 345
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 172 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 172 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather172]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d86_s0_row345_col109

theorem cell_d86_s2_row345_col110 :
    sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 345 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 345
  have hfun : (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 345 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 345 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 347 r - alphaSelected^3 * unitVector 344 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 347) (unitVector 344) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 345
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 173 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 172 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather173]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d86_s2_row345_col110

theorem cell_d87_s2_row345_col112 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 345 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 345 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 345
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 345 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 345 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 351 r - alphaSelected^3 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 351) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 345
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 175 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 345 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather175]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s2_row345_col112

theorem cell_d86_s0_row347_col109 :
    sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 347 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 347 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 347
  have hfun : (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 347 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 347 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨86, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 345 r - alphaSelected^1 * unitVector 344 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 345) (unitVector 344) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 347
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 172 347 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 172 347 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather172]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d86_s0_row347_col109

theorem cell_d86_s2_row347_col110 :
    sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 347 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 347 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 347
  have hfun : (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 347 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 347 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 347 r - alphaSelected^3 * unitVector 344 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 347) (unitVector 344) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 347
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 173 347 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 172 347 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather173]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d86_s2_row347_col110

theorem cell_d86_s2_row349_col110 :
    sourceChord halfSelected (direction alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 349 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 349 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 349
  have hfun : (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 349 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 349 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨86, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 347 r - alphaSelected^3 * unitVector 344 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 347) (unitVector 344) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 349
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 173 349 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 172 349 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather173]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d86_s2_row349_col110

theorem cell_d87_s0_row349_col111 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 349 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 349 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 349
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 349 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 349 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 349 r - alphaSelected^1 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 349) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 349
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 174 349 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 349 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather174]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s0_row349_col111

theorem cell_d87_s2_row349_col112 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 349 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 349 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 349
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 349 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 349 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 351 r - alphaSelected^3 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 351) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 349
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 175 349 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 349 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather175]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s2_row349_col112
end
end AspisV8R19.R799ActiveSourceCellsChunk11
