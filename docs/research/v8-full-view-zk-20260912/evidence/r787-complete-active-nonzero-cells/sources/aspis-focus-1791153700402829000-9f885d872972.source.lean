import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R748GatherExpand00
import AspisV8R19.R748GatherExpand01
import AspisV8R19.R748GatherNested00
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk00
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748FiniteGatherSchedules
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherNested00
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d32_s0_row128_col7 :
    sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 129 r - alphaSelected^1 * unitVector 128 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 129) (unitVector 128) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 128
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 64 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 64 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather64]
  rw [gather64]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d32_s0_row128_col7

theorem cell_d32_s1_row128_col8 :
    sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 130 r - alphaSelected^2 * unitVector 128 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 130) (unitVector 128) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 128
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 65 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 64 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather65]
  rw [gather64]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d32_s1_row128_col8

theorem cell_d47_s1_row128_col35 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (335544320 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 128 = (335544320 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 128
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 128 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 128 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 190 r - alphaSelected^2 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 190) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 128
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 95 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 128 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s1_row128_col35

theorem cell_d32_s0_row130_col7 :
    sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 130 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 130 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 130
  have hfun : (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 130 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 130 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 129 r - alphaSelected^1 * unitVector 128 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 129) (unitVector 128) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 130
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 64 130 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 64 130 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather64]
  rw [gather64]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d32_s0_row130_col7

theorem cell_d32_s1_row130_col8 :
    sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 130 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 130 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 130
  have hfun : (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 130 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 130 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 130 r - alphaSelected^2 * unitVector 128 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 130) (unitVector 128) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 130
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 65 130 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 64 130 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather65]
  rw [gather64]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d32_s1_row130_col8

theorem cell_d47_s2_row130_col221 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 130 = (335544320 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 130 = (335544320 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 130
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 130 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 130 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 191 r - alphaSelected^3 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 191) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 130
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 95 130 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 130 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s2_row130_col221

theorem cell_d32_s0_row132_col7 :
    sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 132 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 132
  have hfun : (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 132 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 132 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 129 r - alphaSelected^1 * unitVector 128 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 129) (unitVector 128) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 132
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 64 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 64 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather64]
  rw [gather64]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d32_s0_row132_col7

theorem cell_d32_s1_row132_col8 :
    sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 132 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 132 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 132
  have hfun : (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 132 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 132 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 130 r - alphaSelected^2 * unitVector 128 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 130) (unitVector 128) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 132
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 65 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 64 132 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather65]
  rw [gather64]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d32_s1_row132_col8

theorem cell_d40_s0_row160_col23 :
    sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 160 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 160
  have hfun : (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 160 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 160 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 161 r - alphaSelected^1 * unitVector 160 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 161) (unitVector 160) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 160
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 80 160 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 80 160 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather80]
  rw [gather80]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d40_s0_row160_col23

theorem cell_d40_s1_row160_col24 :
    sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 160 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 160
  have hfun : (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 160 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 160 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 162 r - alphaSelected^2 * unitVector 160 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 162) (unitVector 160) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 160
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 81 160 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 80 160 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather81]
  rw [gather80]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d40_s1_row160_col24

theorem cell_d47_s1_row160_col35 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 160 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 160 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 160
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 160 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 160 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 190 r - alphaSelected^2 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 190) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 160
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 95 160 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 160 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s1_row160_col35

theorem cell_d40_s0_row162_col23 :
    sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 162 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 162 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 162
  have hfun : (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 162 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 162 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 161 r - alphaSelected^1 * unitVector 160 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 161) (unitVector 160) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 162
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 80 162 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 80 162 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather80]
  rw [gather80]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d40_s0_row162_col23

theorem cell_d40_s1_row162_col24 :
    sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 162 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 162 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 162
  have hfun : (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 162 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 162 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 162 r - alphaSelected^2 * unitVector 160 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 162) (unitVector 160) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 162
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 81 162 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 80 162 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather81]
  rw [gather80]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d40_s1_row162_col24

theorem cell_d47_s2_row162_col221 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 162 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 162 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 162
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 162 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 162 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 191 r - alphaSelected^3 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 191) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 162
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 95 162 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 162 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s2_row162_col221

theorem cell_d40_s0_row164_col23 :
    sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 164 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 164 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 164
  have hfun : (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 164 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 164 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨40, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 161 r - alphaSelected^1 * unitVector 160 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 161) (unitVector 160) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 164
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 80 164 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 80 164 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather80]
  rw [gather80]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d40_s0_row164_col23

theorem cell_d40_s1_row164_col24 :
    sourceChord halfSelected (direction alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 164 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 164 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 164
  have hfun : (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 164 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 164 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨40, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 162 r - alphaSelected^2 * unitVector 160 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 162) (unitVector 160) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 164
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 81 164 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 80 164 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather81]
  rw [gather80]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d40_s1_row164_col24
end
end AspisV8R19.R799ActiveSourceCellsChunk00
