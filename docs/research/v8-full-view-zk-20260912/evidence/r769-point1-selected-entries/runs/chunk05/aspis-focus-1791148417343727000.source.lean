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
namespace AspisV8R19.R769Point1SelectedChunk05
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 161 (direction (227,2)). -/
theorem point1_d227_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 227 1
      (.inr (.inl 1)) = 332136 := by
  unfold sparseObservation
  change (pw 910 - 7^(1+1)*pw 908) - (pw 2 - 7^(1+1)*pw 0) = 332136
  rw [pw_0910, pw_0908, pw_0002, pw0]
  decide
#print axioms point1_d227_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 162 (direction (228,1)). -/
theorem point1_d228_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 228 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 913 - 7^(0+1)*pw 912) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0913, pw_0912, pw_0001, pw0]
  decide
#print axioms point1_d228_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 163 (direction (228,2)). -/
theorem point1_d228_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 228 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 914 - 7^(1+1)*pw 912) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0914, pw_0912, pw_0002, pw0]
  decide
#print axioms point1_d228_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 164 (direction (229,1)). -/
theorem point1_d229_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 229 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 917 - 7^(0+1)*pw 916) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0917, pw_0916, pw_0001, pw0]
  decide
#print axioms point1_d229_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 165 (direction (229,2)). -/
theorem point1_d229_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 229 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 918 - 7^(1+1)*pw 916) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0918, pw_0916, pw_0002, pw0]
  decide
#print axioms point1_d229_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 166 (direction (230,1)). -/
theorem point1_d230_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 230 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 921 - 7^(0+1)*pw 920) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0921, pw_0920, pw_0001, pw0]
  decide
#print axioms point1_d230_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 167 (direction (230,2)). -/
theorem point1_d230_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 230 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 922 - 7^(1+1)*pw 920) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0922, pw_0920, pw_0002, pw0]
  decide
#print axioms point1_d230_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 168 (direction (231,1)). -/
theorem point1_d231_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 231 0
      (.inr (.inl 1)) = 48564 := by
  unfold sparseObservation
  change (pw 925 - 7^(0+1)*pw 924) - (pw 1 - 7^(0+1)*pw 0) = 48564
  rw [pw_0925, pw_0924, pw_0001, pw0]
  decide
#print axioms point1_d231_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 169 (direction (231,2)). -/
theorem point1_d231_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 231 1
      (.inr (.inl 1)) = 331956 := by
  unfold sparseObservation
  change (pw 926 - 7^(1+1)*pw 924) - (pw 2 - 7^(1+1)*pw 0) = 331956
  rw [pw_0926, pw_0924, pw_0002, pw0]
  decide
#print axioms point1_d231_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 170 (direction (232,1)). -/
theorem point1_d232_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 232 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 929 - 7^(0+1)*pw 928) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0929, pw_0928, pw_0001, pw0]
  decide
#print axioms point1_d232_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 171 (direction (232,2)). -/
theorem point1_d232_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 232 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 930 - 7^(1+1)*pw 928) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0930, pw_0928, pw_0002, pw0]
  decide
#print axioms point1_d232_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 172 (direction (233,1)). -/
theorem point1_d233_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 233 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 933 - 7^(0+1)*pw 932) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0933, pw_0932, pw_0001, pw0]
  decide
#print axioms point1_d233_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 173 (direction (233,2)). -/
theorem point1_d233_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 233 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 934 - 7^(1+1)*pw 932) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0934, pw_0932, pw_0002, pw0]
  decide
#print axioms point1_d233_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 174 (direction (234,1)). -/
theorem point1_d234_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 234 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 937 - 7^(0+1)*pw 936) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0937, pw_0936, pw_0001, pw0]
  decide
#print axioms point1_d234_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 175 (direction (234,2)). -/
theorem point1_d234_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 234 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 938 - 7^(1+1)*pw 936) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0938, pw_0936, pw_0002, pw0]
  decide
#print axioms point1_d234_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 176 (direction (235,1)). -/
theorem point1_d235_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 235 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 941 - 7^(0+1)*pw 940) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0941, pw_0940, pw_0001, pw0]
  decide
#print axioms point1_d235_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 177 (direction (235,2)). -/
theorem point1_d235_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 235 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 942 - 7^(1+1)*pw 940) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0942, pw_0940, pw_0002, pw0]
  decide
#print axioms point1_d235_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 178 (direction (236,1)). -/
theorem point1_d236_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 236 0
      (.inr (.inl 1)) = 28224 := by
  unfold sparseObservation
  change (pw 945 - 7^(0+1)*pw 944) - (pw 1 - 7^(0+1)*pw 0) = 28224
  rw [pw_0945, pw_0944, pw_0001, pw0]
  decide
#print axioms point1_d236_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 179 (direction (237,1)). -/
theorem point1_d237_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 237 0
      (.inr (.inl 1)) = 28224 := by
  unfold sparseObservation
  change (pw 949 - 7^(0+1)*pw 948) - (pw 1 - 7^(0+1)*pw 0) = 28224
  rw [pw_0949, pw_0948, pw_0001, pw0]
  decide
#print axioms point1_d237_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 180 (direction (238,1)). -/
theorem point1_d238_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 238 0
      (.inr (.inl 1)) = 49824 := by
  unfold sparseObservation
  change (pw 953 - 7^(0+1)*pw 952) - (pw 1 - 7^(0+1)*pw 0) = 49824
  rw [pw_0953, pw_0952, pw_0001, pw0]
  decide
#print axioms point1_d238_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 181 (direction (238,2)). -/
theorem point1_d238_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 238 1
      (.inr (.inl 1)) = 333216 := by
  unfold sparseObservation
  change (pw 954 - 7^(1+1)*pw 952) - (pw 2 - 7^(1+1)*pw 0) = 333216
  rw [pw_0954, pw_0952, pw_0002, pw0]
  decide
#print axioms point1_d238_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 182 (direction (239,2)). -/
theorem point1_d239_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 239 1
      (.inr (.inl 1)) = 135738 := by
  unfold sparseObservation
  change (pw 958 - 7^(1+1)*pw 956) - (pw 2 - 7^(1+1)*pw 0) = 135738
  rw [pw_0958, pw_0956, pw_0002, pw0]
  decide
#print axioms point1_d239_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 183 (direction (240,1)). -/
theorem point1_d240_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 240 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 961 - 7^(0+1)*pw 960) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0961, pw_0960, pw_0001, pw0]
  decide
#print axioms point1_d240_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 184 (direction (240,2)). -/
theorem point1_d240_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 240 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 962 - 7^(1+1)*pw 960) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0962, pw_0960, pw_0002, pw0]
  decide
#print axioms point1_d240_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 185 (direction (241,1)). -/
theorem point1_d241_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 241 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 965 - 7^(0+1)*pw 964) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0965, pw_0964, pw_0001, pw0]
  decide
#print axioms point1_d241_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 186 (direction (241,2)). -/
theorem point1_d241_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 241 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 966 - 7^(1+1)*pw 964) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0966, pw_0964, pw_0002, pw0]
  decide
#print axioms point1_d241_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 187 (direction (242,1)). -/
theorem point1_d242_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 242 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 969 - 7^(0+1)*pw 968) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0969, pw_0968, pw_0001, pw0]
  decide
#print axioms point1_d242_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 188 (direction (242,2)). -/
theorem point1_d242_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 242 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 970 - 7^(1+1)*pw 968) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0970, pw_0968, pw_0002, pw0]
  decide
#print axioms point1_d242_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 189 (direction (243,1)). -/
theorem point1_d243_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 243 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 973 - 7^(0+1)*pw 972) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0973, pw_0972, pw_0001, pw0]
  decide
#print axioms point1_d243_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 190 (direction (243,2)). -/
theorem point1_d243_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 243 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 974 - 7^(1+1)*pw 972) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0974, pw_0972, pw_0002, pw0]
  decide
#print axioms point1_d243_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 191 (direction (244,1)). -/
theorem point1_d244_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 244 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 977 - 7^(0+1)*pw 976) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0977, pw_0976, pw_0001, pw0]
  decide
#print axioms point1_d244_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 192 (direction (244,2)). -/
theorem point1_d244_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 244 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 978 - 7^(1+1)*pw 976) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0978, pw_0976, pw_0002, pw0]
  decide
#print axioms point1_d244_s1
end AspisV8R19.R769Point1SelectedChunk05
