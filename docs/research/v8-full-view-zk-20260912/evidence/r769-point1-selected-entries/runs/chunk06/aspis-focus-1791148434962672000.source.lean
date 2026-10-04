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
namespace AspisV8R19.R769Point1SelectedChunk06
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 193 (direction (245,1)). -/
theorem point1_d245_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 245 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 981 - 7^(0+1)*pw 980) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0981, pw_0980, pw_0001, pw0]
  decide
#print axioms point1_d245_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 194 (direction (245,2)). -/
theorem point1_d245_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 245 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 982 - 7^(1+1)*pw 980) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0982, pw_0980, pw_0002, pw0]
  decide
#print axioms point1_d245_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 195 (direction (246,1)). -/
theorem point1_d246_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 246 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 985 - 7^(0+1)*pw 984) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0985, pw_0984, pw_0001, pw0]
  decide
#print axioms point1_d246_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 196 (direction (246,2)). -/
theorem point1_d246_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 246 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 986 - 7^(1+1)*pw 984) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0986, pw_0984, pw_0002, pw0]
  decide
#print axioms point1_d246_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 197 (direction (247,1)). -/
theorem point1_d247_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 247 0
      (.inr (.inl 1)) = 1073790200 := by
  unfold sparseObservation
  change (pw 989 - 7^(0+1)*pw 988) - (pw 1 - 7^(0+1)*pw 0) = 1073790200
  rw [pw_0989, pw_0988, pw_0001, pw0]
  decide
#print axioms point1_d247_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 198 (direction (247,2)). -/
theorem point1_d247_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 247 1
      (.inr (.inl 1)) = 1074073592 := by
  unfold sparseObservation
  change (pw 990 - 7^(1+1)*pw 988) - (pw 2 - 7^(1+1)*pw 0) = 1074073592
  rw [pw_0990, pw_0988, pw_0002, pw0]
  decide
#print axioms point1_d247_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 199 (direction (248,1)). -/
theorem point1_d248_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 248 0
      (.inr (.inl 1)) = 48404 := by
  unfold sparseObservation
  change (pw 993 - 7^(0+1)*pw 992) - (pw 1 - 7^(0+1)*pw 0) = 48404
  rw [pw_0993, pw_0992, pw_0001, pw0]
  decide
#print axioms point1_d248_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 200 (direction (248,2)). -/
theorem point1_d248_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 248 1
      (.inr (.inl 1)) = 331664 := by
  unfold sparseObservation
  change (pw 994 - 7^(1+1)*pw 992) - (pw 2 - 7^(1+1)*pw 0) = 331664
  rw [pw_0994, pw_0992, pw_0002, pw0]
  decide
#print axioms point1_d248_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 201 (direction (249,1)). -/
theorem point1_d249_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 249 0
      (.inr (.inl 1)) = 48479 := by
  unfold sparseObservation
  change (pw 997 - 7^(0+1)*pw 996) - (pw 1 - 7^(0+1)*pw 0) = 48479
  rw [pw_0997, pw_0996, pw_0001, pw0]
  decide
#print axioms point1_d249_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 202 (direction (249,2)). -/
theorem point1_d249_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 249 1
      (.inr (.inl 1)) = 332047 := by
  unfold sparseObservation
  change (pw 998 - 7^(1+1)*pw 996) - (pw 2 - 7^(1+1)*pw 0) = 332047
  rw [pw_0998, pw_0996, pw_0002, pw0]
  decide
#print axioms point1_d249_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 203 (direction (250,1)). -/
theorem point1_d250_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 250 0
      (.inr (.inl 1)) = 48354 := by
  unfold sparseObservation
  change (pw 1001 - 7^(0+1)*pw 1000) - (pw 1 - 7^(0+1)*pw 0) = 48354
  rw [pw_1001, pw_1000, pw_0001, pw0]
  decide
#print axioms point1_d250_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 204 (direction (250,2)). -/
theorem point1_d250_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 250 1
      (.inr (.inl 1)) = 331944 := by
  unfold sparseObservation
  change (pw 1002 - 7^(1+1)*pw 1000) - (pw 2 - 7^(1+1)*pw 0) = 331944
  rw [pw_1002, pw_1000, pw_0002, pw0]
  decide
#print axioms point1_d250_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 205 (direction (251,1)). -/
theorem point1_d251_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 251 0
      (.inr (.inl 1)) = 48324 := by
  unfold sparseObservation
  change (pw 1005 - 7^(0+1)*pw 1004) - (pw 1 - 7^(0+1)*pw 0) = 48324
  rw [pw_1005, pw_1004, pw_0001, pw0]
  decide
#print axioms point1_d251_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 206 (direction (251,2)). -/
theorem point1_d251_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 251 1
      (.inr (.inl 1)) = 331452 := by
  unfold sparseObservation
  change (pw 1006 - 7^(1+1)*pw 1004) - (pw 2 - 7^(1+1)*pw 0) = 331452
  rw [pw_1006, pw_1004, pw_0002, pw0]
  decide
#print axioms point1_d251_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 207 (direction (252,1)). -/
theorem point1_d252_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 252 0
      (.inr (.inl 1)) = 26744 := by
  unfold sparseObservation
  change (pw 1009 - 7^(0+1)*pw 1008) - (pw 1 - 7^(0+1)*pw 0) = 26744
  rw [pw_1009, pw_1008, pw_0001, pw0]
  decide
#print axioms point1_d252_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 208 (direction (252,3)). -/
theorem point1_d252_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 252 2
      (.inr (.inl 1)) = 1386652 := by
  unfold sparseObservation
  change (pw 1011 - 7^(2+1)*pw 1008) - (pw 3 - 7^(2+1)*pw 0) = 1386652
  rw [pw_1011, pw_1008, pw3, pw0]
  decide
#print axioms point1_d252_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 209 (direction (253,1)). -/
theorem point1_d253_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 253 0
      (.inr (.inl 1)) = 2147455665 := by
  unfold sparseObservation
  change (pw 1013 - 7^(0+1)*pw 1012) - (pw 1 - 7^(0+1)*pw 0) = 2147455665
  rw [pw_1013, pw_1012, pw_0001, pw0]
  decide
#print axioms point1_d253_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 210 (direction (253,3)). -/
theorem point1_d253_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 253 2
      (.inr (.inl 1)) = 2146478026 := by
  unfold sparseObservation
  change (pw 1015 - 7^(2+1)*pw 1012) - (pw 3 - 7^(2+1)*pw 0) = 2146478026
  rw [pw_1015, pw_1012, pw3, pw0]
  decide
#print axioms point1_d253_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 211 (direction (254,1)). -/
theorem point1_d254_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 254 0
      (.inr (.inl 1)) = 2147456635 := by
  unfold sparseObservation
  change (pw 1017 - 7^(0+1)*pw 1016) - (pw 1 - 7^(0+1)*pw 0) = 2147456635
  rw [pw_1017, pw_1016, pw_0001, pw0]
  decide
#print axioms point1_d254_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 212 (direction (254,3)). -/
theorem point1_d254_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 254 2
      (.inr (.inl 1)) = 2146478173 := by
  unfold sparseObservation
  change (pw 1019 - 7^(2+1)*pw 1016) - (pw 3 - 7^(2+1)*pw 0) = 2146478173
  rw [pw_1019, pw_1016, pw3, pw0]
  decide
#print axioms point1_d254_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 213 (direction (254,2)). -/
theorem point1_d254_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 254 1
      (.inr (.inl 1)) = 2147345071 := by
  unfold sparseObservation
  change (pw 1018 - 7^(1+1)*pw 1016) - (pw 2 - 7^(1+1)*pw 0) = 2147345071
  rw [pw_1018, pw_1016, pw_0002, pw0]
  decide
#print axioms point1_d254_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 214 (direction (23,1)). -/
theorem point1_d023_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 0
      (.inr (.inl 1)) = 45 := by
  unfold sparseObservation
  change (pw 93 - 7^(0+1)*pw 92) - (pw 1 - 7^(0+1)*pw 0) = 45
  rw [pw_0093, pw_0092, pw_0001, pw0]
  decide
#print axioms point1_d023_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 215 (direction (23,2)). -/
theorem point1_d023_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 1
      (.inr (.inl 1)) = 45 := by
  unfold sparseObservation
  change (pw 94 - 7^(1+1)*pw 92) - (pw 2 - 7^(1+1)*pw 0) = 45
  rw [pw_0094, pw_0092, pw_0002, pw0]
  decide
#print axioms point1_d023_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 216 (direction (23,3)). -/
theorem point1_d023_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 2
      (.inr (.inl 1)) = 1073741711 := by
  unfold sparseObservation
  change (pw 95 - 7^(2+1)*pw 92) - (pw 3 - 7^(2+1)*pw 0) = 1073741711
  rw [pw_0095, pw_0092, pw3, pw0]
  decide
#print axioms point1_d023_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 217 (direction (24,1)). -/
theorem point1_d024_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 0
      (.inr (.inl 1)) = 2147483527 := by
  unfold sparseObservation
  change (pw 97 - 7^(0+1)*pw 96) - (pw 1 - 7^(0+1)*pw 0) = 2147483527
  rw [pw_0097, pw_0096, pw_0001, pw0]
  decide
#print axioms point1_d024_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 218 (direction (24,2)). -/
theorem point1_d024_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 1
      (.inr (.inl 1)) = 672 := by
  unfold sparseObservation
  change (pw 98 - 7^(1+1)*pw 96) - (pw 2 - 7^(1+1)*pw 0) = 672
  rw [pw_0098, pw_0096, pw_0002, pw0]
  decide
#print axioms point1_d024_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 219 (direction (24,3)). -/
theorem point1_d024_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 2
      (.inr (.inl 1)) = 27444 := by
  unfold sparseObservation
  change (pw 99 - 7^(2+1)*pw 96) - (pw 3 - 7^(2+1)*pw 0) = 27444
  rw [pw_0099, pw_0096, pw3, pw0]
  decide
#print axioms point1_d024_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 228 (direction (27,3)). -/
theorem point1_d027_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 27 2
      (.inr (.inl 1)) = 53028 := by
  unfold sparseObservation
  change (pw 111 - 7^(2+1)*pw 108) - (pw 3 - 7^(2+1)*pw 0) = 53028
  rw [pw_0111, pw_0108, pw3, pw0]
  decide
#print axioms point1_d027_s2
end AspisV8R19.R769Point1SelectedChunk06
