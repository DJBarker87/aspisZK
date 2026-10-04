import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand04
import AspisV8R19.R748GatherNested03
import AspisV8R19.R748SchedulePrototype
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk15
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand04
open AspisV8R19.R748GatherNested03
open AspisV8R19.R748SchedulePrototype
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d125_s2_row505_col129 :
    sourceChord halfSelected (direction alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 505 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 505
  have hfun : (fun r => qPair alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 505 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 505 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨125, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 503 r - alphaSelected^3 * unitVector 500 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 503) (unitVector 500) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 505
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 251 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 250 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather251]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d125_s2_row505_col129

theorem cell_d126_s0_row505_col130 :
    sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 505 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 505
  have hfun : (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 505 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 505 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 505 r - alphaSelected^1 * unitVector 504 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 505) (unitVector 504) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 505
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 252 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 252 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather252]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d126_s0_row505_col130

theorem cell_d126_s2_row505_col131 :
    sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 505 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 505
  have hfun : (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 505 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 505 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 507 r - alphaSelected^3 * unitVector 504 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 507) (unitVector 504) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 505
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 253 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 252 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather253]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d126_s2_row505_col131

theorem cell_d127_s2_row505_col133 :
    sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 505 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 505 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 505
  have hfun : (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 505 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 505 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 511 r - alphaSelected^3 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 511) (unitVector 508) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 505
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 255 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 254 505 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather255]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d127_s2_row505_col133

theorem cell_d126_s0_row507_col130 :
    sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 507 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 507 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 507
  have hfun : (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 507 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 507 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨126, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 505 r - alphaSelected^1 * unitVector 504 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 505) (unitVector 504) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 507
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 252 507 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 252 507 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather252]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d126_s0_row507_col130

theorem cell_d126_s2_row507_col131 :
    sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 507 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 507 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 507
  have hfun : (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 507 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 507 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 507 r - alphaSelected^3 * unitVector 504 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 507) (unitVector 504) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 507
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 253 507 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 252 507 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather253]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d126_s2_row507_col131

theorem cell_d126_s2_row509_col131 :
    sourceChord halfSelected (direction alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 509 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 509 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 509
  have hfun : (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 509 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 509 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨126, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 507 r - alphaSelected^3 * unitVector 504 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 507) (unitVector 504) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 509
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 253 509 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 252 509 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather253]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d126_s2_row509_col131

theorem cell_d127_s0_row509_col132 :
    sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 509 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 509 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 509
  have hfun : (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 509 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 509 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 509 r - alphaSelected^1 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 509) (unitVector 508) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 509
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 254 509 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 254 509 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather254]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d127_s0_row509_col132

theorem cell_d127_s2_row509_col133 :
    sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 509 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 509 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 509
  have hfun : (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 509 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 509 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 511 r - alphaSelected^3 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 511) (unitVector 508) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 509
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 255 509 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 254 509 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather255]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d127_s2_row509_col133

theorem cell_d127_s0_row511_col132 :
    sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 511 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 511 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 511
  have hfun : (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 511 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 511 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨127, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 509 r - alphaSelected^1 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 509) (unitVector 508) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 511
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 254 511 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 254 511 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather254]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d127_s0_row511_col132

theorem cell_d127_s2_row511_col133 :
    sourceChord halfSelected (direction alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 511 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 511 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 511
  have hfun : (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 511 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 511 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨127, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 511 r - alphaSelected^3 * unitVector 508 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 511) (unitVector 508) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 511
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 255 511 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 254 511 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather255]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d127_s2_row511_col133

theorem cell_d156_s1_row626_col134 :
    sourceChord halfSelected (direction alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 626 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 626 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 626
  have hfun : (fun r => qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 626 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 626 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 626 r - alphaSelected^2 * unitVector 624 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 626) (unitVector 624) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 626
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 313 626 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 312 626 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather313]
  rw [gather312]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d156_s1_row626_col134

theorem cell_d159_s2_row626_col141 :
    sourceChord halfSelected (direction alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 626 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 626 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 626
  have hfun : (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 626 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 626 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨159, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 639 r - alphaSelected^3 * unitVector 636 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 639) (unitVector 636) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 626
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 319 626 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 318 626 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather319]
  rw [gather318]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d159_s2_row626_col141

theorem cell_d156_s1_row628_col134 :
    sourceChord halfSelected (direction alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 628 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 628 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 628
  have hfun : (fun r => qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 628 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 628 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨156, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 626 r - alphaSelected^2 * unitVector 624 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 626) (unitVector 624) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 628
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 313 628 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 312 628 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather313]
  rw [gather312]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d156_s1_row628_col134

theorem cell_d157_s0_row628_col135 :
    sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 628 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 628 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 628
  have hfun : (fun r => qPair alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 628 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 628 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨157, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 629 r - alphaSelected^1 * unitVector 628 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 629) (unitVector 628) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 628
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 314 628 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 314 628 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather314]
  rw [gather314]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d157_s0_row628_col135

theorem cell_d157_s1_row628_col136 :
    sourceChord halfSelected (direction alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 628 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 628 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 628
  have hfun : (fun r => qPair alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 628 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 628 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨157, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 630 r - alphaSelected^2 * unitVector 628 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 630) (unitVector 628) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 628
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 315 628 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 314 628 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather315]
  rw [gather314]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d157_s1_row628_col136
end
end AspisV8R19.R799ActiveSourceCellsChunk15
