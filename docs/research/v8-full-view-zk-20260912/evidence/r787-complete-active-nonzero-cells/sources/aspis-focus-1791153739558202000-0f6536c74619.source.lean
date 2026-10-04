import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherExpand03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk07
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

theorem cell_d72_s2_row293_col83 :
    sourceChord halfSelected (direction alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 293 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 293 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 293
  have hfun : (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 293 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 293 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨72, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 291 r - alphaSelected^3 * unitVector 288 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 291) (unitVector 288) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 293
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 145 293 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 144 293 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather145]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d72_s2_row293_col83

theorem cell_d73_s0_row293_col84 :
    sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 293 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 293 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 293
  have hfun : (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 293 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 293 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 293 r - alphaSelected^1 * unitVector 292 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 293) (unitVector 292) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 293
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 146 293 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 146 293 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather146]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d73_s0_row293_col84

theorem cell_d73_s2_row293_col85 :
    sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 293 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 293 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 293
  have hfun : (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 293 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 293 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 295 r - alphaSelected^3 * unitVector 292 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 295) (unitVector 292) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 293
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 147 293 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 146 293 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather147]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d73_s2_row293_col85

theorem cell_d73_s0_row295_col84 :
    sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 295 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 295 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 295
  have hfun : (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 295 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 295 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 293 r - alphaSelected^1 * unitVector 292 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 293) (unitVector 292) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 295
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 146 295 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 146 295 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather146]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d73_s0_row295_col84

theorem cell_d73_s2_row295_col85 :
    sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 295 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 295 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 295
  have hfun : (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 295 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 295 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 295 r - alphaSelected^3 * unitVector 292 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 295) (unitVector 292) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 295
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 147 295 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 146 295 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather147]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d73_s2_row295_col85

theorem cell_d73_s2_row297_col85 :
    sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 297 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 297
  have hfun : (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 297 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 297 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 295 r - alphaSelected^3 * unitVector 292 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 295) (unitVector 292) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 297
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 147 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 146 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather147]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d73_s2_row297_col85

theorem cell_d74_s0_row297_col86 :
    sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 297 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 297
  have hfun : (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 297 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 297 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 297 r - alphaSelected^1 * unitVector 296 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 297) (unitVector 296) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 297
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 148 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 148 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather148]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d74_s0_row297_col86

theorem cell_d74_s2_row297_col87 :
    sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 297 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 297
  have hfun : (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 297 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 297 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 299 r - alphaSelected^3 * unitVector 296 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 299) (unitVector 296) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 297
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 149 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 148 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather149]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d74_s2_row297_col87

theorem cell_d75_s2_row297_col89 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 297 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 297
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 297 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 297 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 303 r - alphaSelected^3 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 303) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 297
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 151 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 297 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather151]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s2_row297_col89

theorem cell_d74_s0_row299_col86 :
    sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 299 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 299 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 299
  have hfun : (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 299 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 299 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 297 r - alphaSelected^1 * unitVector 296 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 297) (unitVector 296) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 299
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 148 299 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 148 299 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather148]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d74_s0_row299_col86

theorem cell_d74_s2_row299_col87 :
    sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 299 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 299 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 299
  have hfun : (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 299 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 299 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 299 r - alphaSelected^3 * unitVector 296 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 299) (unitVector 296) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 299
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 149 299 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 148 299 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather149]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d74_s2_row299_col87

theorem cell_d74_s2_row301_col87 :
    sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 301 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 301 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 301
  have hfun : (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 301 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 301 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 299 r - alphaSelected^3 * unitVector 296 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 299) (unitVector 296) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 301
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 149 301 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 148 301 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather149]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d74_s2_row301_col87

theorem cell_d75_s0_row301_col88 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 301 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 301 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 301
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 301 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 301 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 301 r - alphaSelected^1 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 301) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 301
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 150 301 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 301 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather150]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s0_row301_col88

theorem cell_d75_s2_row301_col89 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 301 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 301 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 301
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 301 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 301 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 303 r - alphaSelected^3 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 303) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 301
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 151 301 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 301 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather151]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s2_row301_col89

theorem cell_d75_s0_row303_col88 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 303 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 303 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 303
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 303 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 303 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 301 r - alphaSelected^1 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 301) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 303
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 150 303 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 303 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather150]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s0_row303_col88

theorem cell_d75_s2_row303_col89 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 303 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 303 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 303
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 303 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 303 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 303 r - alphaSelected^3 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 303) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 303
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 151 303 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 303 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather151]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s2_row303_col89
end
end AspisV8R19.R799ActiveSourceCellsChunk07
