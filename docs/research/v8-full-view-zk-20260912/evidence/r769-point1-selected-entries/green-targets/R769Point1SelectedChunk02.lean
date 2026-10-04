import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R760PointWeightPrototype
import AspisV8R19.R760PointWeightChunk00
import AspisV8R19.R760PointWeightChunk01
import AspisV8R19.R760PointWeightChunk02
import AspisV8R19.R760PointWeightChunk03
import AspisV8R19.R760PointWeightChunk04
import AspisV8R19.R760PointWeightChunk05
import AspisV8R19.R760PointWeightChunk06
import AspisV8R19.R760PointWeightChunk07
import AspisV8R19.R760PointWeightChunk08
import AspisV8R19.R760PointWeightChunk09
import AspisV8R19.R760PointWeightChunk10

open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R760PointWeightPrototype
open AspisV8R19.R760PointWeightChunk00 AspisV8R19.R760PointWeightChunk01
open AspisV8R19.R760PointWeightChunk02 AspisV8R19.R760PointWeightChunk03
open AspisV8R19.R760PointWeightChunk04 AspisV8R19.R760PointWeightChunk05
open AspisV8R19.R760PointWeightChunk06 AspisV8R19.R760PointWeightChunk07
open AspisV8R19.R760PointWeightChunk08 AspisV8R19.R760PointWeightChunk09
open AspisV8R19.R760PointWeightChunk10
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R769Point1SelectedChunk02
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 64 (direction (62,3)). -/
theorem point1_d062_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 2
      (.inr (.inl 1)) = 2146447729 := by
  unfold sparseObservation
  change (pw 251 - 7^(2+1)*pw 248) - (pw 3 - 7^(2+1)*pw 0) = 2146447729
  rw [pw_0251, pw_0248, pw3, pw0]
  decide
#print axioms point1_d062_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 65 (direction (63,1)). -/
theorem point1_d063_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 63 0
      (.inr (.inl 1)) = 1073717564 := by
  unfold sparseObservation
  change (pw 253 - 7^(0+1)*pw 252) - (pw 1 - 7^(0+1)*pw 0) = 1073717564
  rw [pw_0253, pw_0252, pw_0001, pw0]
  decide
#print axioms point1_d063_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 66 (direction (64,1)). -/
theorem point1_d064_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 64 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 257 - 7^(0+1)*pw 256) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0257, pw_0256, pw_0001, pw0]
  decide
#print axioms point1_d064_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 67 (direction (64,3)). -/
theorem point1_d064_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 64 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 259 - 7^(2+1)*pw 256) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0259, pw_0256, pw3, pw0]
  decide
#print axioms point1_d064_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 68 (direction (65,1)). -/
theorem point1_d065_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 65 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 261 - 7^(0+1)*pw 260) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0261, pw_0260, pw_0001, pw0]
  decide
#print axioms point1_d065_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 69 (direction (65,3)). -/
theorem point1_d065_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 65 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 263 - 7^(2+1)*pw 260) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0263, pw_0260, pw3, pw0]
  decide
#print axioms point1_d065_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 70 (direction (66,1)). -/
theorem point1_d066_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 66 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 265 - 7^(0+1)*pw 264) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0265, pw_0264, pw_0001, pw0]
  decide
#print axioms point1_d066_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 71 (direction (66,3)). -/
theorem point1_d066_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 66 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 267 - 7^(2+1)*pw 264) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0267, pw_0264, pw3, pw0]
  decide
#print axioms point1_d066_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 72 (direction (67,1)). -/
theorem point1_d067_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 67 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 269 - 7^(0+1)*pw 268) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0269, pw_0268, pw_0001, pw0]
  decide
#print axioms point1_d067_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 73 (direction (67,3)). -/
theorem point1_d067_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 67 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 271 - 7^(2+1)*pw 268) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0271, pw_0268, pw3, pw0]
  decide
#print axioms point1_d067_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 74 (direction (68,1)). -/
theorem point1_d068_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 68 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 273 - 7^(0+1)*pw 272) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0273, pw_0272, pw_0001, pw0]
  decide
#print axioms point1_d068_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 75 (direction (68,3)). -/
theorem point1_d068_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 68 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 275 - 7^(2+1)*pw 272) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0275, pw_0272, pw3, pw0]
  decide
#print axioms point1_d068_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 76 (direction (69,1)). -/
theorem point1_d069_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 69 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 277 - 7^(0+1)*pw 276) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0277, pw_0276, pw_0001, pw0]
  decide
#print axioms point1_d069_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 77 (direction (69,3)). -/
theorem point1_d069_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 69 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 279 - 7^(2+1)*pw 276) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0279, pw_0276, pw3, pw0]
  decide
#print axioms point1_d069_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 78 (direction (70,1)). -/
theorem point1_d070_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 70 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 281 - 7^(0+1)*pw 280) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0281, pw_0280, pw_0001, pw0]
  decide
#print axioms point1_d070_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 79 (direction (70,3)). -/
theorem point1_d070_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 70 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 283 - 7^(2+1)*pw 280) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0283, pw_0280, pw3, pw0]
  decide
#print axioms point1_d070_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 80 (direction (71,1)). -/
theorem point1_d071_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 71 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 285 - 7^(0+1)*pw 284) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0285, pw_0284, pw_0001, pw0]
  decide
#print axioms point1_d071_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 81 (direction (71,3)). -/
theorem point1_d071_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 71 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 287 - 7^(2+1)*pw 284) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0287, pw_0284, pw3, pw0]
  decide
#print axioms point1_d071_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 82 (direction (72,1)). -/
theorem point1_d072_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 72 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 289 - 7^(0+1)*pw 288) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0289, pw_0288, pw_0001, pw0]
  decide
#print axioms point1_d072_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 83 (direction (72,3)). -/
theorem point1_d072_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 72 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 291 - 7^(2+1)*pw 288) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0291, pw_0288, pw3, pw0]
  decide
#print axioms point1_d072_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 84 (direction (73,1)). -/
theorem point1_d073_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 73 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 293 - 7^(0+1)*pw 292) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0293, pw_0292, pw_0001, pw0]
  decide
#print axioms point1_d073_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 85 (direction (73,3)). -/
theorem point1_d073_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 73 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 295 - 7^(2+1)*pw 292) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0295, pw_0292, pw3, pw0]
  decide
#print axioms point1_d073_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 86 (direction (74,1)). -/
theorem point1_d074_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 74 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 297 - 7^(0+1)*pw 296) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0297, pw_0296, pw_0001, pw0]
  decide
#print axioms point1_d074_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 87 (direction (74,3)). -/
theorem point1_d074_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 74 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 299 - 7^(2+1)*pw 296) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0299, pw_0296, pw3, pw0]
  decide
#print axioms point1_d074_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 88 (direction (75,1)). -/
theorem point1_d075_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 75 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 301 - 7^(0+1)*pw 300) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0301, pw_0300, pw_0001, pw0]
  decide
#print axioms point1_d075_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 89 (direction (75,3)). -/
theorem point1_d075_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 75 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 303 - 7^(2+1)*pw 300) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0303, pw_0300, pw3, pw0]
  decide
#print axioms point1_d075_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 90 (direction (76,1)). -/
theorem point1_d076_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 76 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 305 - 7^(0+1)*pw 304) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0305, pw_0304, pw_0001, pw0]
  decide
#print axioms point1_d076_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 91 (direction (76,3)). -/
theorem point1_d076_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 76 2
      (.inr (.inl 1)) = 2146490335 := by
  unfold sparseObservation
  change (pw 307 - 7^(2+1)*pw 304) - (pw 3 - 7^(2+1)*pw 0) = 2146490335
  rw [pw_0307, pw_0304, pw3, pw0]
  decide
#print axioms point1_d076_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 92 (direction (77,3)). -/
theorem point1_d077_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 77 2
      (.inr (.inl 1)) = 2147478175 := by
  unfold sparseObservation
  change (pw 311 - 7^(2+1)*pw 308) - (pw 3 - 7^(2+1)*pw 0) = 2147478175
  rw [pw_0311, pw_0308, pw3, pw0]
  decide
#print axioms point1_d077_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 93 (direction (78,1)). -/
theorem point1_d078_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 78 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 313 - 7^(0+1)*pw 312) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0313, pw_0312, pw_0001, pw0]
  decide
#print axioms point1_d078_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 94 (direction (78,3)). -/
theorem point1_d078_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 78 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 315 - 7^(2+1)*pw 312) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0315, pw_0312, pw3, pw0]
  decide
#print axioms point1_d078_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 95 (direction (79,1)). -/
theorem point1_d079_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 79 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 317 - 7^(0+1)*pw 316) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0317, pw_0316, pw_0001, pw0]
  decide
#print axioms point1_d079_s0
end AspisV8R19.R769Point1SelectedChunk02
