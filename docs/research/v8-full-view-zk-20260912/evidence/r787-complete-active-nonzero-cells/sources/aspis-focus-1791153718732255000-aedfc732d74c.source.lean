import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherExpand03
import AspisV8R19.R748SchedulePrototype
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk03
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherExpand03
open AspisV8R19.R748SchedulePrototype
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d61_s0_row247_col61 :
    sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 247 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 247 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 247
  have hfun : (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 247 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 247 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 245 r - alphaSelected^1 * unitVector 244 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 245) (unitVector 244) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 247
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 122 247 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 122 247 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather122]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d61_s0_row247_col61

theorem cell_d61_s2_row247_col62 :
    sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 247 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 247 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 247
  have hfun : (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 247 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 247 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 247 r - alphaSelected^3 * unitVector 244 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 247) (unitVector 244) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 247
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 123 247 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 122 247 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather123]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d61_s2_row247_col62

theorem cell_d61_s2_row249_col62 :
    sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 249 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 249 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 249
  have hfun : (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 249 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 249 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 247 r - alphaSelected^3 * unitVector 244 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 247) (unitVector 244) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 249
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 123 249 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 122 249 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather123]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d61_s2_row249_col62

theorem cell_d62_s0_row249_col63 :
    sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 249 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 249 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 249
  have hfun : (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 249 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 249 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 249 r - alphaSelected^1 * unitVector 248 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 249) (unitVector 248) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 249
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 124 249 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 124 249 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather124]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d62_s0_row249_col63

theorem cell_d62_s2_row249_col64 :
    sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 249 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 249 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 249
  have hfun : (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 249 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 249 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 251 r - alphaSelected^3 * unitVector 248 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 251) (unitVector 248) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 249
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 125 249 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 124 249 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather125]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d62_s2_row249_col64

theorem cell_d62_s0_row251_col63 :
    sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 251 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 251 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 251
  have hfun : (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 251 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 251 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 249 r - alphaSelected^1 * unitVector 248 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 249) (unitVector 248) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 251
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 124 251 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 124 251 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather124]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d62_s0_row251_col63

theorem cell_d62_s2_row251_col64 :
    sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 251 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 251 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 251
  have hfun : (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 251 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 251 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 251 r - alphaSelected^3 * unitVector 248 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 251) (unitVector 248) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 251
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 125 251 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 124 251 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather125]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d62_s2_row251_col64

theorem cell_d62_s2_row253_col64 :
    sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 253 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 253 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 253
  have hfun : (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 253 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 253 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 251 r - alphaSelected^3 * unitVector 248 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 251) (unitVector 248) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 253
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 125 253 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 124 253 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather125]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d62_s2_row253_col64

theorem cell_d63_s0_row253_col65 :
    sourceChord halfSelected (direction alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 253 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 253 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 253
  have hfun : (fun r => qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 253 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 253 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 253 r - alphaSelected^1 * unitVector 252 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 253) (unitVector 252) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 253
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 126 253 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 126 253 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather126]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d63_s0_row253_col65

theorem cell_d64_s0_row257_col66 :
    sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 257 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 257 r - alphaSelected^1 * unitVector 256 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 257) (unitVector 256) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 128 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 128 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather128]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d64_s0_row257_col66

theorem cell_d64_s2_row257_col67 :
    sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 257 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨64, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 259 r - alphaSelected^3 * unitVector 256 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 259) (unitVector 256) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 129 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 128 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather129]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d64_s2_row257_col67

theorem cell_d65_s2_row257_col69 :
    sourceChord halfSelected (direction alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 257 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨65, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 263 r - alphaSelected^3 * unitVector 260 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 263) (unitVector 260) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 131 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 130 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather131]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d65_s2_row257_col69

theorem cell_d67_s2_row257_col73 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 257 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 271 r - alphaSelected^3 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 271) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 135 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather135]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s2_row257_col73

theorem cell_d71_s2_row257_col81 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (671088640 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 257 = (671088640 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 287 r - alphaSelected^3 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 287) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 143 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather143]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s2_row257_col81

theorem cell_d79_s2_row257_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 257 = (335544320 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 257 = (335544320 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 257
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 257 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 257 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 257
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 257 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row257_col96

theorem cell_d64_s0_row259_col66 :
    sourceChord halfSelected (direction alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 259 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 259 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 259
  have hfun : (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 259 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 259 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨64, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 257 r - alphaSelected^1 * unitVector 256 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 257) (unitVector 256) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 259
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 128 259 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 128 259 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather128]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d64_s0_row259_col66
end
end AspisV8R19.R799ActiveSourceCellsChunk03
