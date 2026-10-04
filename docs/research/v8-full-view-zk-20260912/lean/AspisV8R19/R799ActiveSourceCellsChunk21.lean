import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand05
import AspisV8R19.R748GatherNested03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk21
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand05
open AspisV8R19.R748GatherNested03
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d228_s1_row912_col163 :
    sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 912 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 912
  have hfun : (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 912 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 912 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 914 r - alphaSelected^2 * unitVector 912 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 914) (unitVector 912) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 912
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 457 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 456 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather457]
  rw [gather456]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d228_s1_row912_col163

theorem cell_d229_s0_row912_col164 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 912 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 912
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 912 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 912 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 917 r - alphaSelected^1 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 917) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 912
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 458 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather458]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s0_row912_col164

theorem cell_d229_s1_row912_col165 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 912 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 912
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 912 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 912 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 918 r - alphaSelected^2 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 918) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 912
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 459 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather459]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s1_row912_col165

theorem cell_d231_s0_row912_col168 :
    sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 912
  have hfun : (fun r => qPair alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 912 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 912 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 925 r - alphaSelected^1 * unitVector 924 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 925) (unitVector 924) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 912
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 462 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 462 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather462]
  rw [gather462]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d231_s0_row912_col168

theorem cell_d231_s1_row912_col169 :
    sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 912 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 912
  have hfun : (fun r => qPair alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 912 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 912 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 926 r - alphaSelected^2 * unitVector 924 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 926) (unitVector 924) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 912
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 463 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 462 912 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather463]
  rw [gather462]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d231_s1_row912_col169

theorem cell_d228_s0_row914_col162 :
    sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 914 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 914 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 914
  have hfun : (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 914 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 914 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 913 r - alphaSelected^1 * unitVector 912 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 913) (unitVector 912) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 914
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 456 914 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 456 914 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather456]
  rw [gather456]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d228_s0_row914_col162

theorem cell_d228_s1_row914_col163 :
    sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 914 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 914 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 914
  have hfun : (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 914 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 914 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 914 r - alphaSelected^2 * unitVector 912 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 914) (unitVector 912) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 914
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 457 914 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 456 914 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather457]
  rw [gather456]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d228_s1_row914_col163

theorem cell_d228_s0_row916_col162 :
    sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 916 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 916
  have hfun : (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 916 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 916 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨228, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 913 r - alphaSelected^1 * unitVector 912 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 913) (unitVector 912) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 916
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 456 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 456 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather456]
  rw [gather456]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d228_s0_row916_col162

theorem cell_d228_s1_row916_col163 :
    sourceChord halfSelected (direction alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 916 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 916
  have hfun : (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 916 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 916 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨228, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 914 r - alphaSelected^2 * unitVector 912 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 914) (unitVector 912) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 916
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 457 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 456 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather457]
  rw [gather456]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d228_s1_row916_col163

theorem cell_d229_s0_row916_col164 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 916 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 916
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 916 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 916 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 917 r - alphaSelected^1 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 917) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 916
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 458 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather458]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s0_row916_col164

theorem cell_d229_s1_row916_col165 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 916 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 916 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 916
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 916 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 916 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 918 r - alphaSelected^2 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 918) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 916
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 459 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 916 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather459]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s1_row916_col165

theorem cell_d229_s0_row918_col164 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 918 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 918 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 918
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 918 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 918 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 917 r - alphaSelected^1 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 917) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 918
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 458 918 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 918 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather458]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s0_row918_col164

theorem cell_d229_s1_row918_col165 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 918 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 918 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 918
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 918 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 918 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 918 r - alphaSelected^2 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 918) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 918
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 459 918 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 918 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather459]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s1_row918_col165

theorem cell_d229_s0_row920_col164 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 920
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 920 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 920 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 917 r - alphaSelected^1 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 917) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 920
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 458 920 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 920 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather458]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s0_row920_col164

theorem cell_d229_s1_row920_col165 :
    sourceChord halfSelected (direction alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 920 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 920
  have hfun : (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 920 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 920 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨229, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 918 r - alphaSelected^2 * unitVector 916 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 918) (unitVector 916) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 920
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 459 920 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 458 920 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather459]
  rw [gather458]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d229_s1_row920_col165

theorem cell_d230_s0_row920_col166 :
    sourceChord halfSelected (direction alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 920 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 920 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 920
  have hfun : (fun r => qPair alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 920 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 920 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨230, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 921 r - alphaSelected^1 * unitVector 920 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 921) (unitVector 920) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 920
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 460 920 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 460 920 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather460]
  rw [gather460]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d230_s0_row920_col166
end
end AspisV8R19.R799ActiveSourceCellsChunk21
