import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R748GatherExpand01
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherNested00
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk01
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748FiniteGatherSchedules
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherNested00
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d44_s0_row176_col31 :
    sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 176 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 176
  have hfun : (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 176 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 176 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 177 r - alphaSelected^1 * unitVector 176 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 177) (unitVector 176) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 176
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 88 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 88 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather88]
  rw [gather88]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d44_s0_row176_col31

theorem cell_d44_s1_row176_col32 :
    sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 176 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 176
  have hfun : (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 176 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 176 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 178 r - alphaSelected^2 * unitVector 176 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 178) (unitVector 176) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 176
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 89 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 88 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather89]
  rw [gather88]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d44_s1_row176_col32

theorem cell_d47_s1_row176_col35 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 176
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 176 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 176 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 190 r - alphaSelected^2 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 190) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 176
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 95 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s1_row176_col35

theorem cell_d44_s0_row178_col31 :
    sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 178 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 178 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 178
  have hfun : (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 178 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 178 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 177 r - alphaSelected^1 * unitVector 176 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 177) (unitVector 176) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 178
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 88 178 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 88 178 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather88]
  rw [gather88]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d44_s0_row178_col31

theorem cell_d44_s1_row178_col32 :
    sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 178 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 178 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 178
  have hfun : (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 178 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 178 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 178 r - alphaSelected^2 * unitVector 176 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 178) (unitVector 176) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 178
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 89 178 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 88 178 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather89]
  rw [gather88]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d44_s1_row178_col32

theorem cell_d47_s2_row178_col221 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 178 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 178 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 178
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 178 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 178 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 191 r - alphaSelected^3 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 191) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 178
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 95 178 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 178 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s2_row178_col221

theorem cell_d44_s0_row180_col31 :
    sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 180 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 180 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 180
  have hfun : (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 180 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 180 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨44, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 177 r - alphaSelected^1 * unitVector 176 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 177) (unitVector 176) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 180
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 88 180 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 88 180 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather88]
  rw [gather88]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d44_s0_row180_col31

theorem cell_d44_s1_row180_col32 :
    sourceChord halfSelected (direction alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 180 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 180 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 180
  have hfun : (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 180 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 180 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨44, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 178 r - alphaSelected^2 * unitVector 176 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 178) (unitVector 176) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 180
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 89 180 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 88 180 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather89]
  rw [gather88]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d44_s1_row180_col32

theorem cell_d46_s0_row184_col34 :
    sourceChord halfSelected (direction alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 184 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 184 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 184
  have hfun : (fun r => qPair alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 184 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 184 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨46, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 185 r - alphaSelected^1 * unitVector 184 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 185) (unitVector 184) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 184
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 92 184 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 92 184 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather92]
  rw [gather92]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d46_s0_row184_col34

theorem cell_d47_s1_row184_col35 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 184 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 184 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 184
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 184 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 184 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 190 r - alphaSelected^2 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 190) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 184
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 95 184 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 184 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s1_row184_col35

theorem cell_d47_s1_row190_col35 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 190 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 190 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 190
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 190 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 190 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 190 r - alphaSelected^2 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 190) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 190
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 95 190 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 190 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s1_row190_col35

theorem cell_d47_s2_row190_col221 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 190 = (1073740106 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 190 = (1073740106 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 190
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 190 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 190 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 191 r - alphaSelected^3 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 191) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 190
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 95 190 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 190 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s2_row190_col221

theorem cell_d48_s1_row194_col36 :
    sourceChord halfSelected (direction alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 194 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 194 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 194
  have hfun : (fun r => qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 194 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 194 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 194 r - alphaSelected^2 * unitVector 192 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 194) (unitVector 192) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 194
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 97 194 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 96 194 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather97]
  rw [gather96]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d48_s1_row194_col36

theorem cell_d47_s2_row194_col221 :
    sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 194 = (335544320 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 194 = (335544320 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 194
  have hfun : (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 194 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 194 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 191 r - alphaSelected^3 * unitVector 188 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 191) (unitVector 188) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 194
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 95 194 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 94 194 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather95]
  rw [gather94]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d47_s2_row194_col221

theorem cell_d48_s1_row196_col36 :
    sourceChord halfSelected (direction alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 196 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 196 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 196
  have hfun : (fun r => qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 196 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 196 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 194 r - alphaSelected^2 * unitVector 192 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 194) (unitVector 192) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 196
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 97 196 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 96 196 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather97]
  rw [gather96]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d48_s1_row196_col36

theorem cell_d58_s1_row234_col56 :
    sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 234 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 234 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 234
  have hfun : (fun r => qPair alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 234 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 234 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 234 r - alphaSelected^2 * unitVector 232 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 234) (unitVector 232) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 234
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 117 234 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 116 234 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather117]
  rw [gather116]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d58_s1_row234_col56
end
end AspisV8R19.R799ActiveSourceCellsChunk01
