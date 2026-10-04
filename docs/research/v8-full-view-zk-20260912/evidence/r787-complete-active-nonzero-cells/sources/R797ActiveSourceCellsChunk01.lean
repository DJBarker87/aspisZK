import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand00
import AspisV8R19.R748GatherExpand01
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherNested00
import AspisV8R19.R748GatherNested01
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R797ActiveSourceCellsChunk01
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherNested00
open AspisV8R19.R748GatherNested01
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d31_s0_row126_col5 :
    sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 126 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 126 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 126
  have hfun : (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 126 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 126 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 125 r - alphaSelected^1 * unitVector 124 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 125) (unitVector 124) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 126
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 62 126 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 62 126 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather62]
  rw [gather62]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d31_s0_row126_col5

theorem cell_d31_s1_row126_col6 :
    sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 126 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 126 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 126
  have hfun : (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 126 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 126 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 126 r - alphaSelected^2 * unitVector 124 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 126) (unitVector 124) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 126
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 63 126 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 62 126 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather63]
  rw [gather62]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d31_s1_row126_col6

theorem cell_d31_s0_row128_col5 :
    sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 125 r - alphaSelected^1 * unitVector 124 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 125) (unitVector 124) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 128
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 62 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 62 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather62]
  rw [gather62]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d31_s0_row128_col5

theorem cell_d31_s1_row128_col6 :
    sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 126 r - alphaSelected^2 * unitVector 124 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 126) (unitVector 124) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 128
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 63 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 62 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather63]
  rw [gather62]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d31_s1_row128_col6

theorem cell_d33_s0_row128_col9 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 133 r - alphaSelected^1 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 133) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 128
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 66 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather66]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s0_row128_col9

theorem cell_d33_s1_row128_col10 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 134 r - alphaSelected^2 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 134) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 128
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 67 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather67]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s1_row128_col10

theorem cell_d35_s0_row128_col13 :
    sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 141 r - alphaSelected^1 * unitVector 140 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 141) (unitVector 140) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 128
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 70 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 70 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather70]
  rw [gather70]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d35_s0_row128_col13

theorem cell_d35_s1_row128_col14 :
    sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 142 r - alphaSelected^2 * unitVector 140 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 142) (unitVector 140) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 128
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 71 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 70 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather71]
  rw [gather70]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d35_s1_row128_col14

theorem cell_d39_s0_row128_col21 :
    sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 157 r - alphaSelected^1 * unitVector 156 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 157) (unitVector 156) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 128
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 78 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 78 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather78]
  rw [gather78]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d39_s0_row128_col21

theorem cell_d39_s1_row128_col22 :
    sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 158 r - alphaSelected^2 * unitVector 156 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 158) (unitVector 156) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 128
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 79 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 78 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather79]
  rw [gather78]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d39_s1_row128_col22

theorem cell_d63_s0_row128_col65 :
    sourceChord halfSelected (direction alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 253 r - alphaSelected^1 * unitVector 252 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 253) (unitVector 252) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 128
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 126 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 126 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather126]
  rw [gather126]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d63_s0_row128_col65

theorem cell_d33_s0_row132_col9 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 132 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 132
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 132 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 132 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 133 r - alphaSelected^1 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 133) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 132
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 66 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather66]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s0_row132_col9

theorem cell_d33_s1_row132_col10 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 132 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 132
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 132 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 132 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 134 r - alphaSelected^2 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 134) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 132
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 67 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather67]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s1_row132_col10

theorem cell_d33_s0_row134_col9 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 134 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 134 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 134
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 134 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 134 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 133 r - alphaSelected^1 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 133) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 134
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 66 134 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 134 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather66]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s0_row134_col9

theorem cell_d33_s1_row134_col10 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 134 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 134 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 134
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 134 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 134 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 134 r - alphaSelected^2 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 134) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 134
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 67 134 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 134 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather67]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s1_row134_col10

theorem cell_d33_s0_row136_col9 :
    sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 136 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 136 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 136
  have hfun : (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 136 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 136 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 133 r - alphaSelected^1 * unitVector 132 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 133) (unitVector 132) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 136
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 66 136 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 66 136 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather66]
  rw [gather66]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d33_s0_row136_col9
end
end AspisV8R19.R797ActiveSourceCellsChunk01
