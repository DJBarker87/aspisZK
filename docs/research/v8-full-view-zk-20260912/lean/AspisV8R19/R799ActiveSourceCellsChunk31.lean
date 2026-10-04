import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand06
import AspisV8R19.R748GatherExpand07
import AspisV8R19.R748GatherNested04
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk31
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand06
open AspisV8R19.R748GatherExpand07
open AspisV8R19.R748GatherNested04
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d251_s1_row1004_col206 :
    sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1004 = (1073741483 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1004 = (1073741483 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1004
  have hfun : (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1004 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 1004 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 1006 r - alphaSelected^2 * unitVector 1004 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1006) (unitVector 1004) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 1004
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 503 1004 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 502 1004 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather503]
  rw [gather502]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d251_s1_row1004_col206

theorem cell_d251_s0_row1006_col205 :
    sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1006 = (2147483612 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1006 = (2147483612 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1006
  have hfun : (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1006 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1006 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1005 r - alphaSelected^1 * unitVector 1004 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1005) (unitVector 1004) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1006
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 502 1006 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 502 1006 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather502]
  rw [gather502]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d251_s0_row1006_col205

theorem cell_d251_s1_row1006_col206 :
    sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1006 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1006 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1006
  have hfun : (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1006 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 1006 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 1006 r - alphaSelected^2 * unitVector 1004 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1006) (unitVector 1004) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 1006
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 503 1006 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 502 1006 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather503]
  rw [gather502]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d251_s1_row1006_col206

theorem cell_d251_s0_row1008_col205 :
    sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1008 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1008
  have hfun : (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1008 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1008 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1005 r - alphaSelected^1 * unitVector 1004 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1005) (unitVector 1004) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1008
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 502 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 502 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather502]
  rw [gather502]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d251_s0_row1008_col205

theorem cell_d251_s1_row1008_col206 :
    sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1008 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩)) (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1008
  have hfun : (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1008 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨1, by decide⟩ 1008 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 1006 r - alphaSelected^2 * unitVector 1004 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1006) (unitVector 1004) (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 1008
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 503 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 502 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather503]
  rw [gather502]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d251_s1_row1008_col206

theorem cell_d252_s0_row1008_col207 :
    sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1008 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1008
  have hfun : (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1008 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1008 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1009 r - alphaSelected^1 * unitVector 1008 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1009) (unitVector 1008) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1008
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 504 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 504 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather504]
  rw [gather504]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d252_s0_row1008_col207

theorem cell_d252_s2_row1008_col208 :
    sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (2147481246 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1008 = (2147481246 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1008
  have hfun : (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1008 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1008 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1011 r - alphaSelected^3 * unitVector 1008 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1011) (unitVector 1008) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1008
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 505 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 504 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather505]
  rw [gather504]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d252_s2_row1008_col208

theorem cell_d253_s0_row1008_col209 :
    sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1008 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1008
  have hfun : (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1008 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1008 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1013 r - alphaSelected^1 * unitVector 1012 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1013) (unitVector 1012) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1008
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 506 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 506 1008 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gatherGather506]
  rw [gather506]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d253_s0_row1008_col209

theorem cell_d252_s0_row1011_col207 :
    sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1011 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1011 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1011
  have hfun : (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1011 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1011 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1009 r - alphaSelected^1 * unitVector 1008 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1009) (unitVector 1008) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1011
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 504 1011 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 504 1011 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather504]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d252_s0_row1011_col207

theorem cell_d252_s2_row1011_col208 :
    sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1011 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1011 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1011
  have hfun : (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1011 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1011 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1011 r - alphaSelected^3 * unitVector 1008 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1011) (unitVector 1008) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1011
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 505 1011 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 504 1011 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather505]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d252_s2_row1011_col208

theorem cell_d252_s2_row1013_col208 :
    sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1013 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1013 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1013
  have hfun : (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1013 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1013 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1011 r - alphaSelected^3 * unitVector 1008 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1011) (unitVector 1008) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1013
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 505 1013 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 504 1013 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather505]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d252_s2_row1013_col208

theorem cell_d253_s0_row1013_col209 :
    sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1013 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1013 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1013
  have hfun : (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1013 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1013 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1013 r - alphaSelected^1 * unitVector 1012 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1013) (unitVector 1012) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1013
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 506 1013 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 506 1013 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather506]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d253_s0_row1013_col209

theorem cell_d253_s2_row1013_col210 :
    sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1013 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1013 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1013
  have hfun : (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1013 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1013 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1015 r - alphaSelected^3 * unitVector 1012 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1015) (unitVector 1012) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1013
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 507 1013 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 506 1013 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather507]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d253_s2_row1013_col210

theorem cell_d253_s0_row1015_col209 :
    sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1015 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1015 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1015
  have hfun : (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1015 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 1015 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 1013 r - alphaSelected^1 * unitVector 1012 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1013) (unitVector 1012) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 1015
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 506 1015 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 506 1015 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather506]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d253_s0_row1015_col209

theorem cell_d253_s2_row1015_col210 :
    sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1015 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1015 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1015
  have hfun : (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1015 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1015 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1015 r - alphaSelected^3 * unitVector 1012 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1015) (unitVector 1012) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1015
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 507 1015 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 506 1015 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather507]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d253_s2_row1015_col210

theorem cell_d253_s2_row1017_col210 :
    sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1017 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 1017 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 1017
  have hfun : (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 1017 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 1017 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨253, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 1015 r - alphaSelected^3 * unitVector 1012 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 1015) (unitVector 1012) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 1017
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 507 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 506 1017 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather507]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d253_s2_row1017_col210
end
end AspisV8R19.R799ActiveSourceCellsChunk31
