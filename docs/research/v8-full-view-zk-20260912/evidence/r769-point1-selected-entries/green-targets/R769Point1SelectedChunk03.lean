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
namespace AspisV8R19.R769Point1SelectedChunk03
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 96 (direction (79,3)). -/
theorem point1_d079_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 79 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 319 - 7^(2+1)*pw 316) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0319, pw_0316, pw3, pw0]
  decide
#print axioms point1_d079_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 97 (direction (80,1)). -/
theorem point1_d080_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 80 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 321 - 7^(0+1)*pw 320) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0321, pw_0320, pw_0001, pw0]
  decide
#print axioms point1_d080_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 98 (direction (80,3)). -/
theorem point1_d080_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 80 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 323 - 7^(2+1)*pw 320) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0323, pw_0320, pw3, pw0]
  decide
#print axioms point1_d080_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 99 (direction (81,1)). -/
theorem point1_d081_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 81 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 325 - 7^(0+1)*pw 324) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0325, pw_0324, pw_0001, pw0]
  decide
#print axioms point1_d081_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 100 (direction (81,3)). -/
theorem point1_d081_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 81 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 327 - 7^(2+1)*pw 324) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0327, pw_0324, pw3, pw0]
  decide
#print axioms point1_d081_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 101 (direction (82,1)). -/
theorem point1_d082_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 82 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 329 - 7^(0+1)*pw 328) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0329, pw_0328, pw_0001, pw0]
  decide
#print axioms point1_d082_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 102 (direction (82,3)). -/
theorem point1_d082_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 82 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 331 - 7^(2+1)*pw 328) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0331, pw_0328, pw3, pw0]
  decide
#print axioms point1_d082_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 103 (direction (83,1)). -/
theorem point1_d083_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 83 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 333 - 7^(0+1)*pw 332) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0333, pw_0332, pw_0001, pw0]
  decide
#print axioms point1_d083_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 104 (direction (83,3)). -/
theorem point1_d083_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 83 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 335 - 7^(2+1)*pw 332) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0335, pw_0332, pw3, pw0]
  decide
#print axioms point1_d083_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 105 (direction (84,1)). -/
theorem point1_d084_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 84 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 337 - 7^(0+1)*pw 336) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0337, pw_0336, pw_0001, pw0]
  decide
#print axioms point1_d084_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 106 (direction (84,3)). -/
theorem point1_d084_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 84 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 339 - 7^(2+1)*pw 336) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0339, pw_0336, pw3, pw0]
  decide
#print axioms point1_d084_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 107 (direction (85,1)). -/
theorem point1_d085_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 85 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 341 - 7^(0+1)*pw 340) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0341, pw_0340, pw_0001, pw0]
  decide
#print axioms point1_d085_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 108 (direction (85,3)). -/
theorem point1_d085_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 85 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 343 - 7^(2+1)*pw 340) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0343, pw_0340, pw3, pw0]
  decide
#print axioms point1_d085_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 109 (direction (86,1)). -/
theorem point1_d086_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 86 0
      (.inr (.inl 1)) = 2147456575 := by
  unfold sparseObservation
  change (pw 345 - 7^(0+1)*pw 344) - (pw 1 - 7^(0+1)*pw 0) = 2147456575
  rw [pw_0345, pw_0344, pw_0001, pw0]
  decide
#print axioms point1_d086_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 110 (direction (86,3)). -/
theorem point1_d086_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 86 2
      (.inr (.inl 1)) = 2146488895 := by
  unfold sparseObservation
  change (pw 347 - 7^(2+1)*pw 344) - (pw 3 - 7^(2+1)*pw 0) = 2146488895
  rw [pw_0347, pw_0344, pw3, pw0]
  decide
#print axioms point1_d086_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 111 (direction (87,1)). -/
theorem point1_d087_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 87 0
      (.inr (.inl 1)) = 2147456545 := by
  unfold sparseObservation
  change (pw 349 - 7^(0+1)*pw 348) - (pw 1 - 7^(0+1)*pw 0) = 2147456545
  rw [pw_0349, pw_0348, pw_0001, pw0]
  decide
#print axioms point1_d087_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 112 (direction (87,3)). -/
theorem point1_d087_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 87 2
      (.inr (.inl 1)) = 2146488970 := by
  unfold sparseObservation
  change (pw 351 - 7^(2+1)*pw 348) - (pw 3 - 7^(2+1)*pw 0) = 2146488970
  rw [pw_0351, pw_0348, pw3, pw0]
  decide
#print axioms point1_d087_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 113 (direction (88,1)). -/
theorem point1_d088_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 88 0
      (.inr (.inl 1)) = 2147456655 := by
  unfold sparseObservation
  change (pw 353 - 7^(0+1)*pw 352) - (pw 1 - 7^(0+1)*pw 0) = 2147456655
  rw [pw_0353, pw_0352, pw_0001, pw0]
  decide
#print axioms point1_d088_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 114 (direction (88,3)). -/
theorem point1_d088_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 88 2
      (.inr (.inl 1)) = 2146470599 := by
  unfold sparseObservation
  change (pw 355 - 7^(2+1)*pw 352) - (pw 3 - 7^(2+1)*pw 0) = 2146470599
  rw [pw_0355, pw_0352, pw3, pw0]
  decide
#print axioms point1_d088_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 115 (direction (89,1)). -/
theorem point1_d089_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 89 0
      (.inr (.inl 1)) = 2147456955 := by
  unfold sparseObservation
  change (pw 357 - 7^(0+1)*pw 356) - (pw 1 - 7^(0+1)*pw 0) = 2147456955
  rw [pw_0357, pw_0356, pw_0001, pw0]
  decide
#print axioms point1_d089_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 116 (direction (89,3)). -/
theorem point1_d089_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 89 2
      (.inr (.inl 1)) = 2146512073 := by
  unfold sparseObservation
  change (pw 359 - 7^(2+1)*pw 356) - (pw 3 - 7^(2+1)*pw 0) = 2146512073
  rw [pw_0359, pw_0356, pw3, pw0]
  decide
#print axioms point1_d089_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 117 (direction (90,1)). -/
theorem point1_d090_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 90 0
      (.inr (.inl 1)) = 2147459335 := by
  unfold sparseObservation
  change (pw 361 - 7^(0+1)*pw 360) - (pw 1 - 7^(0+1)*pw 0) = 2147459335
  rw [pw_0361, pw_0360, pw_0001, pw0]
  decide
#print axioms point1_d090_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 118 (direction (91,1)). -/
theorem point1_d091_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 91 0
      (.inr (.inl 1)) = 2147456335 := by
  unfold sparseObservation
  change (pw 365 - 7^(0+1)*pw 364) - (pw 1 - 7^(0+1)*pw 0) = 2147456335
  rw [pw_0365, pw_0364, pw_0001, pw0]
  decide
#print axioms point1_d091_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 119 (direction (91,3)). -/
theorem point1_d091_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 91 2
      (.inr (.inl 1)) = 2146453303 := by
  unfold sparseObservation
  change (pw 367 - 7^(2+1)*pw 364) - (pw 3 - 7^(2+1)*pw 0) = 2146453303
  rw [pw_0367, pw_0364, pw3, pw0]
  decide
#print axioms point1_d091_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 120 (direction (92,2)). -/
theorem point1_d092_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 92 1
      (.inr (.inl 1)) = 136544 := by
  unfold sparseObservation
  change (pw 370 - 7^(1+1)*pw 368) - (pw 2 - 7^(1+1)*pw 0) = 136544
  rw [pw_0370, pw_0368, pw_0002, pw0]
  decide
#print axioms point1_d092_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 121 (direction (93,1)). -/
theorem point1_d093_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 93 0
      (.inr (.inl 1)) = 48344 := by
  unfold sparseObservation
  change (pw 373 - 7^(0+1)*pw 372) - (pw 1 - 7^(0+1)*pw 0) = 48344
  rw [pw_0373, pw_0372, pw_0001, pw0]
  decide
#print axioms point1_d093_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 122 (direction (93,2)). -/
theorem point1_d093_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 93 1
      (.inr (.inl 1)) = 330328 := by
  unfold sparseObservation
  change (pw 374 - 7^(1+1)*pw 372) - (pw 2 - 7^(1+1)*pw 0) = 330328
  rw [pw_0374, pw_0372, pw_0002, pw0]
  decide
#print axioms point1_d093_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 123 (direction (94,1)). -/
theorem point1_d094_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 94 0
      (.inr (.inl 1)) = 48624 := by
  unfold sparseObservation
  change (pw 377 - 7^(0+1)*pw 376) - (pw 1 - 7^(0+1)*pw 0) = 48624
  rw [pw_0377, pw_0376, pw_0001, pw0]
  decide
#print axioms point1_d094_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 124 (direction (94,2)). -/
theorem point1_d094_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 94 1
      (.inr (.inl 1)) = 330432 := by
  unfold sparseObservation
  change (pw 378 - 7^(1+1)*pw 376) - (pw 2 - 7^(1+1)*pw 0) = 330432
  rw [pw_0378, pw_0376, pw_0002, pw0]
  decide
#print axioms point1_d094_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 125 (direction (95,1)). -/
theorem point1_d095_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 95 0
      (.inr (.inl 1)) = 49794 := by
  unfold sparseObservation
  change (pw 381 - 7^(0+1)*pw 380) - (pw 1 - 7^(0+1)*pw 0) = 49794
  rw [pw_0381, pw_0380, pw_0001, pw0]
  decide
#print axioms point1_d095_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 126 (direction (95,2)). -/
theorem point1_d095_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 95 1
      (.inr (.inl 1)) = 335298 := by
  unfold sparseObservation
  change (pw 382 - 7^(1+1)*pw 380) - (pw 2 - 7^(1+1)*pw 0) = 335298
  rw [pw_0382, pw_0380, pw_0002, pw0]
  decide
#print axioms point1_d095_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 127 (direction (124,3)). -/
theorem point1_d124_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 124 2
      (.inr (.inl 1)) = 2147459879 := by
  unfold sparseObservation
  change (pw 499 - 7^(2+1)*pw 496) - (pw 3 - 7^(2+1)*pw 0) = 2147459879
  rw [pw_0499, pw_0496, pw3, pw0]
  decide
#print axioms point1_d124_s2
end AspisV8R19.R769Point1SelectedChunk03
