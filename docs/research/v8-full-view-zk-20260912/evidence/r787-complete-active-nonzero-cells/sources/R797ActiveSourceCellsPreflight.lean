import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand00
import AspisV8R19.R748GatherExpand02
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R797ActiveSourceCellsPreflight
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand02
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d28_s1_row114 :
    sourceChord halfSelected (direction alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 114 = (2147483409 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩) r -
        qPair alphaSelected 0 (⟨1, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 114 = (2147483409 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩))
      (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 114
  have hfun : (fun r => qPair alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩) r -
      qPair alphaSelected 0 (⟨1, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩) r -
      (1 : M) * qPair alphaSelected 0 (⟨1, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 114 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ ⟨1, by decide⟩ 114 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩) =
      (fun r => unitVector 114 r - alphaSelected^2 * unitVector 112 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 114) (unitVector 112)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^2) 114
  rw [hdiff2]
  rw [sourceChord_unit_even_sourceGather halfSelected 57 114 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 56 114 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [gather57]
  rw [gather56]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d28_s1_row114

theorem cell_d27_s2_row114 :
    sourceChord halfSelected (direction alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 114 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩) r -
        qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 114 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩))
      (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 114
  have hfun : (fun r => qPair alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩) r -
      qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩) r -
      (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 114 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ ⟨2, by decide⟩ 114 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 111 r - alphaSelected^3 * unitVector 108 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 111) (unitVector 108)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 114
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 55 114 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 54 114 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [gather55]
  rw [gather54]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d27_s2_row114

theorem cell_d29_s0_row116 :
    sourceChord halfSelected (direction alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 116 = (1073741772 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩) r -
        qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 116 = (1073741772 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩))
      (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 116
  have hfun : (fun r => qPair alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩) r -
      qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩) r -
      (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 116 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ ⟨0, by decide⟩ 116 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨29, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 117 r - alphaSelected^1 * unitVector 116 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 117) (unitVector 116)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 116
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 58 116 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 58 116 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [gather58]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d29_s0_row116

theorem cell_d60_s0_row243 :
    sourceChord halfSelected (direction alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 243 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩) r -
        qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 243 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩))
      (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 243
  have hfun : (fun r => qPair alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩) r -
      qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩) r -
      (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 243 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        ⟨0, by decide⟩ ⟨0, by decide⟩ 243 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨60, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 241 r - alphaSelected^1 * unitVector 240 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 241) (unitVector 240)
      (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 243
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 120 243 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 120 243 (by decide)
      (7 : M) (5 : M) (-5 : M)]
  rw [gather120]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d60_s0_row243
end
end AspisV8R19.R797ActiveSourceCellsPreflight
