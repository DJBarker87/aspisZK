import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand01
import AspisV8R19.R748GatherNested00
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R798ActiveSourceCellsChunk06
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherNested00
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d43_s1_row172_col30 :
    sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 172 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 172 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 172
  have hfun : (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 172 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 172 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 174 r - alphaSelected^2 * unitVector 172 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 174) (unitVector 172) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 172
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 87 172 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 86 172 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather87]
  rw [gather86]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d43_s1_row172_col30

theorem cell_d43_s0_row174_col29 :
    sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 174 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 174 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 174
  have hfun : (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 174 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 174 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 173 r - alphaSelected^1 * unitVector 172 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 173) (unitVector 172) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 174
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 86 174 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 86 174 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather86]
  rw [gather86]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d43_s0_row174_col29

theorem cell_d43_s1_row174_col30 :
    sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 174 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 174 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 174
  have hfun : (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 174 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 174 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 174 r - alphaSelected^2 * unitVector 172 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 174) (unitVector 172) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 174
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 87 174 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 86 174 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather87]
  rw [gather86]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d43_s1_row174_col30

theorem cell_d43_s0_row176_col29 :
    sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 176
  have hfun : (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 176 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 176 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨43, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 173 r - alphaSelected^1 * unitVector 172 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 173) (unitVector 172) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 176
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 86 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 86 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather86]
  rw [gather86]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d43_s0_row176_col29

theorem cell_d43_s1_row176_col30 :
    sourceChord halfSelected (direction alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 176 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 176
  have hfun : (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 176 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 176 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨43, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 174 r - alphaSelected^2 * unitVector 172 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 174) (unitVector 172) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 176
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 87 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 86 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather87]
  rw [gather86]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d43_s1_row176_col30

theorem cell_d45_s0_row176_col33 :
    sourceChord halfSelected (direction alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 176 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 176 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 176
  have hfun : (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 176 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 176 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 181 r - alphaSelected^1 * unitVector 180 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 181) (unitVector 180) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 176
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 90 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 90 176 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather90]
  rw [gather90]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d45_s0_row176_col33

theorem cell_d45_s0_row180_col33 :
    sourceChord halfSelected (direction alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 180 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 180 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 180
  have hfun : (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 180 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 180 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 181 r - alphaSelected^1 * unitVector 180 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 181) (unitVector 180) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 180
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 90 180 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 90 180 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather90]
  rw [gather90]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d45_s0_row180_col33

theorem cell_d45_s0_row184_col33 :
    sourceChord halfSelected (direction alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 184 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 184 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 184
  have hfun : (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 184 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 184 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨45, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 181 r - alphaSelected^1 * unitVector 180 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 181) (unitVector 180) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 184
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 90 184 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 90 184 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather90]
  rw [gather90]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d45_s0_row184_col33

theorem cell_d49_s0_row196_col37 :
    sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 196 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 196 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 196
  have hfun : (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 196 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 196 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 197 r - alphaSelected^1 * unitVector 196 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 197) (unitVector 196) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 196
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 98 196 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 98 196 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather98]
  rw [gather98]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d49_s0_row196_col37

theorem cell_d49_s1_row196_col38 :
    sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 196 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 196 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 196
  have hfun : (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 196 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 196 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 198 r - alphaSelected^2 * unitVector 196 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 198) (unitVector 196) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 196
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 99 196 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 98 196 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather99]
  rw [gather98]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d49_s1_row196_col38

theorem cell_d49_s0_row198_col37 :
    sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 198 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 198 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 198
  have hfun : (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 198 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 198 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 197 r - alphaSelected^1 * unitVector 196 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 197) (unitVector 196) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 198
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 98 198 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 98 198 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather98]
  rw [gather98]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d49_s0_row198_col37

theorem cell_d49_s1_row198_col38 :
    sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 198 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 198 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 198
  have hfun : (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 198 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 198 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 198 r - alphaSelected^2 * unitVector 196 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 198) (unitVector 196) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 198
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 99 198 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 98 198 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather99]
  rw [gather98]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d49_s1_row198_col38

theorem cell_d49_s0_row200_col37 :
    sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 200
  have hfun : (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 200 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 200 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 197 r - alphaSelected^1 * unitVector 196 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 197) (unitVector 196) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 200
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 98 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 98 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather98]
  rw [gather98]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d49_s0_row200_col37

theorem cell_d49_s1_row200_col38 :
    sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 200
  have hfun : (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 200 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 200 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 198 r - alphaSelected^2 * unitVector 196 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 198) (unitVector 196) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 200
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 99 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 98 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather99]
  rw [gather98]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d49_s1_row200_col38

theorem cell_d50_s0_row200_col39 :
    sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 200 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 200
  have hfun : (fun r => qPair alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 200 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 200 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 201 r - alphaSelected^1 * unitVector 200 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 201) (unitVector 200) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 200
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 100 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 100 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather100]
  rw [gather100]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d50_s0_row200_col39

theorem cell_d50_s1_row200_col40 :
    sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 200 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 200
  have hfun : (fun r => qPair alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 200 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 200 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 202 r - alphaSelected^2 * unitVector 200 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 202) (unitVector 200) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 200
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 101 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 100 200 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather101]
  rw [gather100]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d50_s1_row200_col40
end
end AspisV8R19.R798ActiveSourceCellsChunk06
