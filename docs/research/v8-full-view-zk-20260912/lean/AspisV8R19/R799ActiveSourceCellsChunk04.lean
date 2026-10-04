import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand02
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk04
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand02
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d64_s2_row259_col67 :
    sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 259 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 259 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 259
  have hfun : (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 259 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 259 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 259 r - alphaSelected^3 * unitVector 256 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 259) (unitVector 256) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 259
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 129 259 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 128 259 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather129]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d64_s2_row259_col67

theorem cell_d64_s2_row261_col67 :
    sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 261 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 261 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 261
  have hfun : (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 261 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 261 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 259 r - alphaSelected^3 * unitVector 256 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 259) (unitVector 256) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 261
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 129 261 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 128 261 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather129]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d64_s2_row261_col67

theorem cell_d65_s0_row261_col68 :
    sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 261 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 261 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 261
  have hfun : (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 261 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 261 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 261 r - alphaSelected^1 * unitVector 260 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 261) (unitVector 260) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 261
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 130 261 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 130 261 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather130]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d65_s0_row261_col68

theorem cell_d65_s2_row261_col69 :
    sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 261 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 261 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 261
  have hfun : (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 261 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 261 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 263 r - alphaSelected^3 * unitVector 260 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 263) (unitVector 260) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 261
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 131 261 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 130 261 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather131]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d65_s2_row261_col69

theorem cell_d65_s0_row263_col68 :
    sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 263 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 263 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 263
  have hfun : (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 263 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 263 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨65, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 261 r - alphaSelected^1 * unitVector 260 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 261) (unitVector 260) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 263
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 130 263 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 130 263 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather130]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d65_s0_row263_col68

theorem cell_d65_s2_row263_col69 :
    sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 263 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 263 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 263
  have hfun : (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 263 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 263 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 263 r - alphaSelected^3 * unitVector 260 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 263) (unitVector 260) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 263
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 131 263 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 130 263 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather131]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d65_s2_row263_col69

theorem cell_d65_s2_row265_col69 :
    sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 265 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 265
  have hfun : (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 265 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 265 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 263 r - alphaSelected^3 * unitVector 260 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 263) (unitVector 260) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 265
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 131 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 130 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather131]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d65_s2_row265_col69

theorem cell_d66_s0_row265_col70 :
    sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 265 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 265
  have hfun : (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 265 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 265 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 265 r - alphaSelected^1 * unitVector 264 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 265) (unitVector 264) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 265
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 132 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 132 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather132]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d66_s0_row265_col70

theorem cell_d66_s2_row265_col71 :
    sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 265 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 265
  have hfun : (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 265 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 265 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 267 r - alphaSelected^3 * unitVector 264 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 267) (unitVector 264) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 265
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 133 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 132 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather133]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d66_s2_row265_col71

theorem cell_d67_s2_row265_col73 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 265 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 265 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 265
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 265 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 265 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 271 r - alphaSelected^3 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 271) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 265
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 135 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 265 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather135]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s2_row265_col73

theorem cell_d66_s0_row267_col70 :
    sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 267 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 267 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 267
  have hfun : (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 267 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 267 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨66, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 265 r - alphaSelected^1 * unitVector 264 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 265) (unitVector 264) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 267
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 132 267 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 132 267 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather132]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d66_s0_row267_col70

theorem cell_d66_s2_row267_col71 :
    sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 267 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 267 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 267
  have hfun : (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 267 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 267 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 267 r - alphaSelected^3 * unitVector 264 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 267) (unitVector 264) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 267
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 133 267 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 132 267 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather133]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d66_s2_row267_col71

theorem cell_d66_s2_row269_col71 :
    sourceChord halfSelected (direction alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 269 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 269 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 269
  have hfun : (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 269 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 269 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨66, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 267 r - alphaSelected^3 * unitVector 264 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 267) (unitVector 264) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 269
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 133 269 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 132 269 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather133]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d66_s2_row269_col71

theorem cell_d67_s0_row269_col72 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 269 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 269 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 269
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 269 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 269 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 269 r - alphaSelected^1 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 269) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 269
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 134 269 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 269 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather134]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s0_row269_col72

theorem cell_d67_s2_row269_col73 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 269 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 269 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 269
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 269 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 269 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 271 r - alphaSelected^3 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 271) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 269
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 135 269 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 269 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather135]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s2_row269_col73

theorem cell_d67_s0_row271_col72 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 271 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 271 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 271
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 271 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 271 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 269 r - alphaSelected^1 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 269) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 271
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 134 271 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 271 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather134]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s0_row271_col72
end
end AspisV8R19.R799ActiveSourceCellsChunk04
