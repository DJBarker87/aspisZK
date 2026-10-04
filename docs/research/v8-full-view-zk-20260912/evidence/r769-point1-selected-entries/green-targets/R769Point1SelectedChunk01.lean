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
namespace AspisV8R19.R769Point1SelectedChunk01
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 32 (direction (44,2)). -/
theorem point1_d044_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 44 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 178 - 7^(1+1)*pw 176) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0178, pw_0176, pw_0002, pw0]
  decide
#print axioms point1_d044_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 33 (direction (45,1)). -/
theorem point1_d045_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 45 0
      (.inr (.inl 1)) = 28224 := by
  unfold sparseObservation
  change (pw 181 - 7^(0+1)*pw 180) - (pw 1 - 7^(0+1)*pw 0) = 28224
  rw [pw_0181, pw_0180, pw_0001, pw0]
  decide
#print axioms point1_d045_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 34 (direction (46,1)). -/
theorem point1_d046_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 46 0
      (.inr (.inl 1)) = 29664 := by
  unfold sparseObservation
  change (pw 185 - 7^(0+1)*pw 184) - (pw 1 - 7^(0+1)*pw 0) = 29664
  rw [pw_0185, pw_0184, pw_0001, pw0]
  decide
#print axioms point1_d046_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 35 (direction (47,2)). -/
theorem point1_d047_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 1
      (.inr (.inl 1)) = 135738 := by
  unfold sparseObservation
  change (pw 190 - 7^(1+1)*pw 188) - (pw 2 - 7^(1+1)*pw 0) = 135738
  rw [pw_0190, pw188, pw_0002, pw0]
  decide
#print axioms point1_d047_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 36 (direction (48,2)). -/
theorem point1_d048_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 48 1
      (.inr (.inl 1)) = 135648 := by
  unfold sparseObservation
  change (pw 194 - 7^(1+1)*pw 192) - (pw 2 - 7^(1+1)*pw 0) = 135648
  rw [pw_0194, pw_0192, pw_0002, pw0]
  decide
#print axioms point1_d048_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 37 (direction (49,1)). -/
theorem point1_d049_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 0
      (.inr (.inl 1)) = 49104 := by
  unfold sparseObservation
  change (pw 197 - 7^(0+1)*pw 196) - (pw 1 - 7^(0+1)*pw 0) = 49104
  rw [pw_0197, pw_0196, pw_0001, pw0]
  decide
#print axioms point1_d049_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 38 (direction (49,2)). -/
theorem point1_d049_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 1
      (.inr (.inl 1)) = 332496 := by
  unfold sparseObservation
  change (pw 198 - 7^(1+1)*pw 196) - (pw 2 - 7^(1+1)*pw 0) = 332496
  rw [pw_0198, pw_0196, pw_0002, pw0]
  decide
#print axioms point1_d049_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 39 (direction (50,1)). -/
theorem point1_d050_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 201 - 7^(0+1)*pw 200) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0201, pw_0200, pw_0001, pw0]
  decide
#print axioms point1_d050_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 40 (direction (50,2)). -/
theorem point1_d050_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 202 - 7^(1+1)*pw 200) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0202, pw_0200, pw_0002, pw0]
  decide
#print axioms point1_d050_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 41 (direction (51,1)). -/
theorem point1_d051_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 0
      (.inr (.inl 1)) = 48744 := by
  unfold sparseObservation
  change (pw 205 - 7^(0+1)*pw 204) - (pw 1 - 7^(0+1)*pw 0) = 48744
  rw [pw_0205, pw_0204, pw_0001, pw0]
  decide
#print axioms point1_d051_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 42 (direction (51,2)). -/
theorem point1_d051_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 1
      (.inr (.inl 1)) = 332136 := by
  unfold sparseObservation
  change (pw 206 - 7^(1+1)*pw 204) - (pw 2 - 7^(1+1)*pw 0) = 332136
  rw [pw_0206, pw_0204, pw_0002, pw0]
  decide
#print axioms point1_d051_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 43 (direction (52,1)). -/
theorem point1_d052_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 209 - 7^(0+1)*pw 208) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0209, pw_0208, pw_0001, pw0]
  decide
#print axioms point1_d052_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 44 (direction (52,2)). -/
theorem point1_d052_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 210 - 7^(1+1)*pw 208) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0210, pw_0208, pw_0002, pw0]
  decide
#print axioms point1_d052_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 45 (direction (53,1)). -/
theorem point1_d053_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 213 - 7^(0+1)*pw 212) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0213, pw_0212, pw_0001, pw0]
  decide
#print axioms point1_d053_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 46 (direction (53,2)). -/
theorem point1_d053_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 214 - 7^(1+1)*pw 212) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0214, pw_0212, pw_0002, pw0]
  decide
#print axioms point1_d053_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 47 (direction (54,1)). -/
theorem point1_d054_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 217 - 7^(0+1)*pw 216) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0217, pw_0216, pw_0001, pw0]
  decide
#print axioms point1_d054_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 48 (direction (54,2)). -/
theorem point1_d054_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 218 - 7^(1+1)*pw 216) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0218, pw_0216, pw_0002, pw0]
  decide
#print axioms point1_d054_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 49 (direction (55,1)). -/
theorem point1_d055_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 0
      (.inr (.inl 1)) = 1073790365 := by
  unfold sparseObservation
  change (pw 221 - 7^(0+1)*pw 220) - (pw 1 - 7^(0+1)*pw 0) = 1073790365
  rw [pw_0221, pw_0220, pw_0001, pw0]
  decide
#print axioms point1_d055_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 50 (direction (55,2)). -/
theorem point1_d055_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 1
      (.inr (.inl 1)) = 1074073757 := by
  unfold sparseObservation
  change (pw 222 - 7^(1+1)*pw 220) - (pw 2 - 7^(1+1)*pw 0) = 1074073757
  rw [pw_0222, pw_0220, pw_0002, pw0]
  decide
#print axioms point1_d055_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 51 (direction (56,1)). -/
theorem point1_d056_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 0
      (.inr (.inl 1)) = 48444 := by
  unfold sparseObservation
  change (pw 225 - 7^(0+1)*pw 224) - (pw 1 - 7^(0+1)*pw 0) = 48444
  rw [pw_0225, pw_0224, pw_0001, pw0]
  decide
#print axioms point1_d056_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 52 (direction (56,2)). -/
theorem point1_d056_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 1
      (.inr (.inl 1)) = 331440 := by
  unfold sparseObservation
  change (pw 226 - 7^(1+1)*pw 224) - (pw 2 - 7^(1+1)*pw 0) = 331440
  rw [pw_0226, pw_0224, pw_0002, pw0]
  decide
#print axioms point1_d056_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 53 (direction (57,1)). -/
theorem point1_d057_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 0
      (.inr (.inl 1)) = 48669 := by
  unfold sparseObservation
  change (pw 229 - 7^(0+1)*pw 228) - (pw 1 - 7^(0+1)*pw 0) = 48669
  rw [pw_0229, pw_0228, pw_0001, pw0]
  decide
#print axioms point1_d057_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 54 (direction (57,2)). -/
theorem point1_d057_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 1
      (.inr (.inl 1)) = 332589 := by
  unfold sparseObservation
  change (pw 230 - 7^(1+1)*pw 228) - (pw 2 - 7^(1+1)*pw 0) = 332589
  rw [pw_0230, pw_0228, pw_0002, pw0]
  decide
#print axioms point1_d057_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 55 (direction (58,1)). -/
theorem point1_d058_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 0
      (.inr (.inl 1)) = 48294 := by
  unfold sparseObservation
  change (pw 233 - 7^(0+1)*pw 232) - (pw 1 - 7^(0+1)*pw 0) = 48294
  rw [pw_0233, pw_0232, pw_0001, pw0]
  decide
#print axioms point1_d058_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 56 (direction (58,2)). -/
theorem point1_d058_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 1
      (.inr (.inl 1)) = 332280 := by
  unfold sparseObservation
  change (pw 234 - 7^(1+1)*pw 232) - (pw 2 - 7^(1+1)*pw 0) = 332280
  rw [pw_0234, pw_0232, pw_0002, pw0]
  decide
#print axioms point1_d058_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 57 (direction (59,1)). -/
theorem point1_d059_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 0
      (.inr (.inl 1)) = 48204 := by
  unfold sparseObservation
  change (pw 237 - 7^(0+1)*pw 236) - (pw 1 - 7^(0+1)*pw 0) = 48204
  rw [pw_0237, pw_0236, pw_0001, pw0]
  decide
#print axioms point1_d059_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 58 (direction (59,2)). -/
theorem point1_d059_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 1
      (.inr (.inl 1)) = 330804 := by
  unfold sparseObservation
  change (pw 238 - 7^(1+1)*pw 236) - (pw 2 - 7^(1+1)*pw 0) = 330804
  rw [pw_0238, pw_0236, pw_0002, pw0]
  decide
#print axioms point1_d059_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 59 (direction (60,1)). -/
theorem point1_d060_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 0
      (.inr (.inl 1)) = 26664 := by
  unfold sparseObservation
  change (pw 241 - 7^(0+1)*pw 240) - (pw 1 - 7^(0+1)*pw 0) = 26664
  rw [pw_0241, pw_0240, pw_0001, pw0]
  decide
#print axioms point1_d060_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 60 (direction (60,3)). -/
theorem point1_d060_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 2
      (.inr (.inl 1)) = 1404948 := by
  unfold sparseObservation
  change (pw 243 - 7^(2+1)*pw 240) - (pw 3 - 7^(2+1)*pw 0) = 1404948
  rw [pw_0243, pw_0240, pw3, pw0]
  decide
#print axioms point1_d060_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 61 (direction (61,1)). -/
theorem point1_d061_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 0
      (.inr (.inl 1)) = 2147455285 := by
  unfold sparseObservation
  change (pw 245 - 7^(0+1)*pw 244) - (pw 1 - 7^(0+1)*pw 0) = 2147455285
  rw [pw_0245, pw_0244, pw_0001, pw0]
  decide
#print axioms point1_d061_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 62 (direction (61,3)). -/
theorem point1_d061_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 2
      (.inr (.inl 1)) = 2146454848 := by
  unfold sparseObservation
  change (pw 247 - 7^(2+1)*pw 244) - (pw 3 - 7^(2+1)*pw 0) = 2146454848
  rw [pw_0247, pw_0244, pw3, pw0]
  decide
#print axioms point1_d061_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 63 (direction (62,1)). -/
theorem point1_d062_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 0
      (.inr (.inl 1)) = 2147456755 := by
  unfold sparseObservation
  change (pw 249 - 7^(0+1)*pw 248) - (pw 1 - 7^(0+1)*pw 0) = 2147456755
  rw [pw_0249, pw_0248, pw_0001, pw0]
  decide
#print axioms point1_d062_s0
end AspisV8R19.R769Point1SelectedChunk01
