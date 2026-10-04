import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R748GatherExpand03
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R799ActiveSourceCellsChunk08
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R748GatherExpand03
noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

theorem cell_d75_s2_row305_col89 :
    sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 305 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 305
  have hfun : (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 305 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 305 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 303 r - alphaSelected^3 * unitVector 300 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 303) (unitVector 300) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 305
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 151 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 150 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather151]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d75_s2_row305_col89

theorem cell_d76_s0_row305_col90 :
    sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 305 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 305
  have hfun : (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 305 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 305 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 305 r - alphaSelected^1 * unitVector 304 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 305) (unitVector 304) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 305
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 152 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 152 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather152]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d76_s0_row305_col90

theorem cell_d76_s2_row305_col91 :
    sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 305 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 305
  have hfun : (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 305 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 305 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 307 r - alphaSelected^3 * unitVector 304 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 307) (unitVector 304) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 305
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 153 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 152 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather153]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d76_s2_row305_col91

theorem cell_d77_s2_row305_col92 :
    sourceChord halfSelected (direction alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 305 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 305
  have hfun : (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 305 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 305 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 311 r - alphaSelected^3 * unitVector 308 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 311) (unitVector 308) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 305
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 155 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 154 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather155]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d77_s2_row305_col92

theorem cell_d79_s2_row305_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (1342177280 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 305 = (1342177280 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 305
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 305 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 305 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 305
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 305 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row305_col96

theorem cell_d76_s0_row307_col90 :
    sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 307 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 307 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 307
  have hfun : (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 307 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 307 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 305 r - alphaSelected^1 * unitVector 304 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 305) (unitVector 304) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 307
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 152 307 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 152 307 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather152]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d76_s0_row307_col90

theorem cell_d76_s2_row307_col91 :
    sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 307 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 307 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 307
  have hfun : (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 307 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 307 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 307 r - alphaSelected^3 * unitVector 304 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 307) (unitVector 304) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 307
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 153 307 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 152 307 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather153]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d76_s2_row307_col91

theorem cell_d77_s2_row311_col92 :
    sourceChord halfSelected (direction alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 311 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 311 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 311
  have hfun : (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 311 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 311 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 311 r - alphaSelected^3 * unitVector 308 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 311) (unitVector 308) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 311
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 155 311 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 154 311 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather155]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d77_s2_row311_col92

theorem cell_d77_s2_row313_col92 :
    sourceChord halfSelected (direction alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 313 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 313
  have hfun : (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 313 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 313 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 311 r - alphaSelected^3 * unitVector 308 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 311) (unitVector 308) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 313
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 155 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 154 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather155]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d77_s2_row313_col92

theorem cell_d78_s0_row313_col93 :
    sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 313 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 313
  have hfun : (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 313 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 313 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 313 r - alphaSelected^1 * unitVector 312 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 313) (unitVector 312) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 313
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 156 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 156 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather156]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d78_s0_row313_col93

theorem cell_d78_s2_row313_col94 :
    sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (1073743541 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 313 = (1073743541 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 313
  have hfun : (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 313 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 313 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 315 r - alphaSelected^3 * unitVector 312 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 315) (unitVector 312) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 313
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 157 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 156 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather157]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d78_s2_row313_col94

theorem cell_d79_s2_row313_col96 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 313 = (536870913 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 313 = (536870913 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 313
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 313 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 313 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 319 r - alphaSelected^3 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 319) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 313
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 159 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 313 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather159]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s2_row313_col96

theorem cell_d78_s0_row315_col93 :
    sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 315 = (5 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 315 = (5 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 315
  have hfun : (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 315 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 315 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨78, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 313 r - alphaSelected^1 * unitVector 312 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 313) (unitVector 312) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 315
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 156 315 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 156 315 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather156]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d78_s0_row315_col93

theorem cell_d78_s2_row315_col94 :
    sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 315 = (7 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 315 = (7 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 315
  have hfun : (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 315 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 315 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 315 r - alphaSelected^3 * unitVector 312 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 315) (unitVector 312) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 315
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 157 315 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 156 315 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather157]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d78_s2_row315_col94

theorem cell_d78_s2_row317_col94 :
    sourceChord halfSelected (direction alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 317 = (1073741826 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 317 = (1073741826 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩)) (qPair alphaSelected 0 (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 317
  have hfun : (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - qPair alphaSelected 0 (⟨2, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨2, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨2, by decide⟩)) (7 : M) (5 : M) (-5 : M) 317 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨2, by decide⟩ 317 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨78, by decide⟩) (⟨2, by decide⟩) =
      (fun r => unitVector 315 r - alphaSelected^3 * unitVector 312 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 315) (unitVector 312) (7 : M) (5 : M) (-5 : M) (alphaSelected^3) 317
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 157 317 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 156 317 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather157]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d78_s2_row317_col94

theorem cell_d79_s0_row317_col95 :
    sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 317 = (42 : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r)
      (7 : M) (5 : M) (-5 : M) 317 = (42 : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩)) (qPair alphaSelected 0 (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) (1 : M) 317
  have hfun : (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) r - qPair alphaSelected 0 (⟨0, by decide⟩) r) =
      (fun r => qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) r - (1 : M) * qPair alphaSelected 0 (⟨0, by decide⟩) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (⟨0, by decide⟩)) (7 : M) (5 : M) (-5 : M) 317 = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected ⟨0, by decide⟩ ⟨0, by decide⟩ 317 (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (⟨79, by decide⟩) (⟨0, by decide⟩) =
      (fun r => unitVector 317 r - alphaSelected^1 * unitVector 316 r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector 317) (unitVector 316) (7 : M) (5 : M) (-5 : M) (alphaSelected^1) 317
  rw [hdiff2]
  rw [sourceChord_unit_odd_sourceGather halfSelected 158 317 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [sourceChord_unit_even_sourceGather halfSelected 158 317 (by decide) (7 : M) (5 : M) (-5 : M)]
  rw [gather158]
  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]
  decide
#print axioms cell_d79_s0_row317_col95
end
end AspisV8R19.R799ActiveSourceCellsChunk08
