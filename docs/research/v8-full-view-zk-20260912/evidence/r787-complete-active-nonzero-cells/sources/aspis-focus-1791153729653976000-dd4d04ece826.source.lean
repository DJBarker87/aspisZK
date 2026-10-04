import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand02
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk05
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand02
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d67_s2_row271_col73 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 271 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 271 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 271
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 271 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 271 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 271 r - alphaSelected^3 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 271) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 271
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 135 271 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 271 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather135]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s2_row271_col73

theorem cell_d67_s2_row273_col73 :
    sourceChord halfSelected (direction alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 273 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 273
  have hfun : (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 273 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 273 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨67, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 271 r - alphaSelected^3 * unitVector 268 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 271) (unitVector 268) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 273
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 135 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 134 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather135]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d67_s2_row273_col73

theorem cell_d68_s0_row273_col74 :
    sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 273 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 273
  have hfun : (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 273 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 273 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 273 r - alphaSelected^1 * unitVector 272 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 273) (unitVector 272) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 273
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 136 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 136 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather136]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d68_s0_row273_col74

theorem cell_d68_s2_row273_col75 :
    sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 273 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 273
  have hfun : (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 273 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 273 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 275 r - alphaSelected^3 * unitVector 272 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 275) (unitVector 272) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 273
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 137 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 136 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather137]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d68_s2_row273_col75

theorem cell_d69_s2_row273_col77 :
    sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 273 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 273
  have hfun : (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 273 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 273 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 279 r - alphaSelected^3 * unitVector 276 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 279) (unitVector 276) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 273
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 139 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 138 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather139]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d69_s2_row273_col77

theorem cell_d71_s2_row273_col81 :
    sourceChord halfSelected (direction alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 273 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 273 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 273
  have hfun : (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 273 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 273 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨71, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 287 r - alphaSelected^3 * unitVector 284 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 287) (unitVector 284) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 273
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 143 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 142 273 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather143]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d71_s2_row273_col81

theorem cell_d68_s0_row275_col74 :
    sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 275 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 275 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 275
  have hfun : (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 275 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 275 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨68, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 273 r - alphaSelected^1 * unitVector 272 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 273) (unitVector 272) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 275
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 136 275 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 136 275 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather136]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d68_s0_row275_col74

theorem cell_d68_s2_row275_col75 :
    sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 275 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 275 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 275
  have hfun : (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 275 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 275 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 275 r - alphaSelected^3 * unitVector 272 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 275) (unitVector 272) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 275
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 137 275 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 136 275 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather137]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d68_s2_row275_col75

theorem cell_d68_s2_row277_col75 :
    sourceChord halfSelected (direction alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 277 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 277 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 277
  have hfun : (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 277 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 277 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨68, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 275 r - alphaSelected^3 * unitVector 272 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 275) (unitVector 272) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 277
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 137 277 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 136 277 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather137]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d68_s2_row277_col75

theorem cell_d69_s0_row277_col76 :
    sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 277 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 277 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 277
  have hfun : (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 277 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 277 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 277 r - alphaSelected^1 * unitVector 276 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 277) (unitVector 276) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 277
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 138 277 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 138 277 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather138]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d69_s0_row277_col76

theorem cell_d69_s2_row277_col77 :
    sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 277 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 277 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 277
  have hfun : (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 277 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 277 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 279 r - alphaSelected^3 * unitVector 276 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 279) (unitVector 276) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 277
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 139 277 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 138 277 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather139]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d69_s2_row277_col77

theorem cell_d69_s0_row279_col76 :
    sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 279 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 279 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 279
  have hfun : (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 279 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 279 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨69, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 277 r - alphaSelected^1 * unitVector 276 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 277) (unitVector 276) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 279
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 138 279 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 138 279 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather138]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d69_s0_row279_col76

theorem cell_d69_s2_row279_col77 :
    sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 279 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 279 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 279
  have hfun : (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 279 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 279 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 279 r - alphaSelected^3 * unitVector 276 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 279) (unitVector 276) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 279
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 139 279 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 138 279 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather139]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d69_s2_row279_col77

theorem cell_d69_s2_row281_col77 :
    sourceChord halfSelected (direction alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 281 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 281
  have hfun : (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 281 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 281 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨69, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 279 r - alphaSelected^3 * unitVector 276 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 279) (unitVector 276) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 281
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 139 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 138 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather139]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d69_s2_row281_col77

theorem cell_d70_s0_row281_col78 :
    sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 281 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 281
  have hfun : (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 281 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 281 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨70, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 281 r - alphaSelected^1 * unitVector 280 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 281) (unitVector 280) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 281
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 140 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 140 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather140]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d70_s0_row281_col78

theorem cell_d70_s2_row281_col79 :
    sourceChord halfSelected (direction alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 281 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 281 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 281
  have hfun : (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 281 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 281 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨70, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 283 r - alphaSelected^3 * unitVector 280 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 283) (unitVector 280) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 281
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 141 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 140 281 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather141]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d70_s2_row281_col79
end
end AspisV8R19.R799ActiveSourceCellsChunk05
