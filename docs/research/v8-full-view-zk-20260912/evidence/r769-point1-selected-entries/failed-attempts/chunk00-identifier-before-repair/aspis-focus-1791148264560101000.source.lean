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
namespace AspisV8R19.R769Point1SelectedChunk00
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 0 (direction (28,2)). -/
theorem point1_d028_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 28 1
      (.inr (.inl 1)) = 134304 := by
  unfold sparseObservation
  change (pw 114 - 7^(1+1)*pw 112) - (pw 2 - 7^(1+1)*pw 0) = 134304
  rw [pw_0114, pw_0112, pw2, pw0]
  decide
#print axioms point1_d028_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 1 (direction (29,1)). -/
theorem point1_d029_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 0
      (.inr (.inl 1)) = 50244 := by
  unfold sparseObservation
  change (pw 117 - 7^(0+1)*pw 116) - (pw 1 - 7^(0+1)*pw 0) = 50244
  rw [pw_0117, pw_0116, pw1, pw0]
  decide
#print axioms point1_d029_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 2 (direction (29,2)). -/
theorem point1_d029_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 1
      (.inr (.inl 1)) = 335748 := by
  unfold sparseObservation
  change (pw 118 - 7^(1+1)*pw 116) - (pw 2 - 7^(1+1)*pw 0) = 335748
  rw [pw_0118, pw_0116, pw2, pw0]
  decide
#print axioms point1_d029_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 3 (direction (30,1)). -/
theorem point1_d030_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 0
      (.inr (.inl 1)) = 48024 := by
  unfold sparseObservation
  change (pw 121 - 7^(0+1)*pw 120) - (pw 1 - 7^(0+1)*pw 0) = 48024
  rw [pw_0121, pw_0120, pw1, pw0]
  decide
#print axioms point1_d030_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 4 (direction (30,2)). -/
theorem point1_d030_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 1
      (.inr (.inl 1)) = 333792 := by
  unfold sparseObservation
  change (pw 122 - 7^(1+1)*pw 120) - (pw 2 - 7^(1+1)*pw 0) = 333792
  rw [pw_0122, pw_0120, pw2, pw0]
  decide
#print axioms point1_d030_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 5 (direction (31,1)). -/
theorem point1_d031_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 0
      (.inr (.inl 1)) = 93384 := by
  unfold sparseObservation
  change (pw 125 - 7^(0+1)*pw 124) - (pw 1 - 7^(0+1)*pw 0) = 93384
  rw [pw_0125, pw_0124, pw1, pw0]
  decide
#print axioms point1_d031_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 6 (direction (31,2)). -/
theorem point1_d031_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 1
      (.inr (.inl 1)) = 610488 := by
  unfold sparseObservation
  change (pw 126 - 7^(1+1)*pw 124) - (pw 2 - 7^(1+1)*pw 0) = 610488
  rw [pw_0126, pw_0124, pw2, pw0]
  decide
#print axioms point1_d031_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 7 (direction (32,1)). -/
theorem point1_d032_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 32 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 129 - 7^(0+1)*pw 128) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0129, pw_0128, pw1, pw0]
  decide
#print axioms point1_d032_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 8 (direction (32,2)). -/
theorem point1_d032_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 32 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 130 - 7^(1+1)*pw 128) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0130, pw_0128, pw2, pw0]
  decide
#print axioms point1_d032_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 9 (direction (33,1)). -/
theorem point1_d033_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 33 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 133 - 7^(0+1)*pw 132) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0133, pw_0132, pw1, pw0]
  decide
#print axioms point1_d033_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 10 (direction (33,2)). -/
theorem point1_d033_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 33 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 134 - 7^(1+1)*pw 132) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0134, pw_0132, pw2, pw0]
  decide
#print axioms point1_d033_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 11 (direction (34,1)). -/
theorem point1_d034_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 34 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 137 - 7^(0+1)*pw 136) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0137, pw_0136, pw1, pw0]
  decide
#print axioms point1_d034_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 12 (direction (34,2)). -/
theorem point1_d034_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 34 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 138 - 7^(1+1)*pw 136) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0138, pw_0136, pw2, pw0]
  decide
#print axioms point1_d034_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 13 (direction (35,1)). -/
theorem point1_d035_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 35 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 141 - 7^(0+1)*pw 140) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0141, pw_0140, pw1, pw0]
  decide
#print axioms point1_d035_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 14 (direction (35,2)). -/
theorem point1_d035_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 35 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 142 - 7^(1+1)*pw 140) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0142, pw_0140, pw2, pw0]
  decide
#print axioms point1_d035_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 15 (direction (36,1)). -/
theorem point1_d036_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 36 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 145 - 7^(0+1)*pw 144) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0145, pw_0144, pw1, pw0]
  decide
#print axioms point1_d036_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 16 (direction (36,2)). -/
theorem point1_d036_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 36 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 146 - 7^(1+1)*pw 144) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0146, pw_0144, pw2, pw0]
  decide
#print axioms point1_d036_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 17 (direction (37,1)). -/
theorem point1_d037_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 37 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 149 - 7^(0+1)*pw 148) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0149, pw_0148, pw1, pw0]
  decide
#print axioms point1_d037_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 18 (direction (37,2)). -/
theorem point1_d037_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 37 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 150 - 7^(1+1)*pw 148) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0150, pw_0148, pw2, pw0]
  decide
#print axioms point1_d037_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 19 (direction (38,1)). -/
theorem point1_d038_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 38 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 153 - 7^(0+1)*pw 152) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0153, pw_0152, pw1, pw0]
  decide
#print axioms point1_d038_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 20 (direction (38,2)). -/
theorem point1_d038_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 38 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 154 - 7^(1+1)*pw 152) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0154, pw_0152, pw2, pw0]
  decide
#print axioms point1_d038_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 21 (direction (39,1)). -/
theorem point1_d039_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 39 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 157 - 7^(0+1)*pw 156) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0157, pw_0156, pw1, pw0]
  decide
#print axioms point1_d039_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 22 (direction (39,2)). -/
theorem point1_d039_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 39 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 158 - 7^(1+1)*pw 156) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0158, pw_0156, pw2, pw0]
  decide
#print axioms point1_d039_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 23 (direction (40,1)). -/
theorem point1_d040_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 40 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 161 - 7^(0+1)*pw 160) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0161, pw_0160, pw1, pw0]
  decide
#print axioms point1_d040_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 24 (direction (40,2)). -/
theorem point1_d040_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 40 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 162 - 7^(1+1)*pw 160) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0162, pw_0160, pw2, pw0]
  decide
#print axioms point1_d040_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 25 (direction (41,1)). -/
theorem point1_d041_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 41 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 165 - 7^(0+1)*pw 164) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0165, pw_0164, pw1, pw0]
  decide
#print axioms point1_d041_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 26 (direction (41,2)). -/
theorem point1_d041_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 41 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 166 - 7^(1+1)*pw 164) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0166, pw_0164, pw2, pw0]
  decide
#print axioms point1_d041_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 27 (direction (42,1)). -/
theorem point1_d042_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 42 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 169 - 7^(0+1)*pw 168) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0169, pw_0168, pw1, pw0]
  decide
#print axioms point1_d042_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 28 (direction (42,2)). -/
theorem point1_d042_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 42 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 170 - 7^(1+1)*pw 168) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0170, pw_0168, pw2, pw0]
  decide
#print axioms point1_d042_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 29 (direction (43,1)). -/
theorem point1_d043_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 43 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 173 - 7^(0+1)*pw 172) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0173, pw_0172, pw1, pw0]
  decide
#print axioms point1_d043_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 30 (direction (43,2)). -/
theorem point1_d043_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 43 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 174 - 7^(1+1)*pw 172) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0174, pw_0172, pw2, pw0]
  decide
#print axioms point1_d043_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 31 (direction (44,1)). -/
theorem point1_d044_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 44 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 177 - 7^(0+1)*pw 176) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0177, pw_0176, pw1, pw0]
  decide
#print axioms point1_d044_s0
end AspisV8R19.R769Point1SelectedChunk00
