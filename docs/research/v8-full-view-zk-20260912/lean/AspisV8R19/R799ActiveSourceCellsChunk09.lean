import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk09
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand03
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d79_s2_row317_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 317 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 317 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 317
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 317 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 317 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 317
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 317 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 317 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row317_col96

theorem cell_d79_s0_row319_col95 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 319 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 319 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 319
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 319 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 319 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 317 r - alphaSelected^1 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 317) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 319
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 158 319 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 319 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather158]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s0_row319_col95

theorem cell_d79_s2_row319_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 319 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 319 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 319
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 319 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 319 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 319
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 319 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 319 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row319_col96

theorem cell_d79_s2_row321_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (335544320 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 321 = (335544320 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 321
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 321 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 321 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 321
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row321_col96

theorem cell_d80_s0_row321_col97 :
    sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 321 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 321
  have hfun : (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 321 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 321 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 321 r - alphaSelected^1 * unitVector 320 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 321) (unitVector 320) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 321
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 160 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 160 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather160]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d80_s0_row321_col97

theorem cell_d80_s2_row321_col98 :
    sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 321 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 321
  have hfun : (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 321 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 321 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 323 r - alphaSelected^3 * unitVector 320 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 323) (unitVector 320) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 321
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 161 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 160 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather161]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d80_s2_row321_col98

theorem cell_d81_s2_row321_col100 :
    sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 321 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 321
  have hfun : (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 321 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 321 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 327 r - alphaSelected^3 * unitVector 324 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 327) (unitVector 324) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 321
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 163 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 162 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather163]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d81_s2_row321_col100

theorem cell_d83_s2_row321_col104 :
    sourceChord halfSelected (direction alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 321 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 321
  have hfun : (fun r => qPair alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 321 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 321 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨83, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 335 r - alphaSelected^3 * unitVector 332 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 335) (unitVector 332) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 321
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 167 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 166 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather167]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d83_s2_row321_col104

theorem cell_d87_s2_row321_col112 :
    sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 321 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 321 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 321
  have hfun : (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 321 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 321 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 351 r - alphaSelected^3 * unitVector 348 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 351) (unitVector 348) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 321
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 175 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 174 321 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather175]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d87_s2_row321_col112

theorem cell_d80_s0_row323_col97 :
    sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 323 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 323 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 323
  have hfun : (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 323 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 323 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨80, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 321 r - alphaSelected^1 * unitVector 320 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 321) (unitVector 320) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 323
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 160 323 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 160 323 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather160]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d80_s0_row323_col97

theorem cell_d80_s2_row323_col98 :
    sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 323 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 323 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 323
  have hfun : (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 323 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 323 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 323 r - alphaSelected^3 * unitVector 320 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 323) (unitVector 320) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 323
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 161 323 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 160 323 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather161]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d80_s2_row323_col98

theorem cell_d80_s2_row325_col98 :
    sourceChord halfSelected (direction alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 325 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 325 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 325
  have hfun : (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 325 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 325 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨80, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 323 r - alphaSelected^3 * unitVector 320 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 323) (unitVector 320) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 325
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 161 325 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 160 325 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather161]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d80_s2_row325_col98

theorem cell_d81_s0_row325_col99 :
    sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 325 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 325 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 325
  have hfun : (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 325 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 325 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 325 r - alphaSelected^1 * unitVector 324 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 325) (unitVector 324) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 325
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 162 325 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 162 325 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather162]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d81_s0_row325_col99

theorem cell_d81_s2_row325_col100 :
    sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 325 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 325 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 325
  have hfun : (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 325 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 325 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 327 r - alphaSelected^3 * unitVector 324 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 327) (unitVector 324) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 325
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 163 325 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 162 325 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather163]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d81_s2_row325_col100

theorem cell_d81_s0_row327_col99 :
    sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 327 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 327 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 327
  have hfun : (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 327 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 327 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨81, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 325 r - alphaSelected^1 * unitVector 324 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 325) (unitVector 324) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 327
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 162 327 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 162 327 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather162]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d81_s0_row327_col99

theorem cell_d81_s2_row327_col100 :
    sourceChord halfSelected (direction alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 327 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 327 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 327
  have hfun : (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 327 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 327 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨81, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 327 r - alphaSelected^3 * unitVector 324 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 327) (unitVector 324) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 327
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 163 327 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 162 327 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather163]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d81_s2_row327_col100
end
end AspisV8R19.R799ActiveSourceCellsChunk09
