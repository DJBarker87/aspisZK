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
namespace AspisV8R19.R769Point1SelectedChunk04
abbrev M := ZMod 2147483647
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 128 (direction (125,1)). -/
theorem point1_d125_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 125 0
      (.inr (.inl 1)) = 2147456955 := by
  unfold sparseObservation
  change (pw 501 - 7^(0+1)*pw 500) - (pw 1 - 7^(0+1)*pw 0) = 2147456955
  rw [pw_0501, pw_0500, pw_0001, pw0]
  decide
#print axioms point1_d125_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 129 (direction (125,3)). -/
theorem point1_d125_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 125 2
      (.inr (.inl 1)) = 2146512793 := by
  unfold sparseObservation
  change (pw 503 - 7^(2+1)*pw 500) - (pw 3 - 7^(2+1)*pw 0) = 2146512793
  rw [pw_0503, pw_0500, pw3, pw0]
  decide
#print axioms point1_d125_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 130 (direction (126,1)). -/
theorem point1_d126_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 126 0
      (.inr (.inl 1)) = 2147456455 := by
  unfold sparseObservation
  change (pw 505 - 7^(0+1)*pw 504) - (pw 1 - 7^(0+1)*pw 0) = 2147456455
  rw [pw_0505, pw_0504, pw_0001, pw0]
  decide
#print axioms point1_d126_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 131 (direction (126,3)). -/
theorem point1_d126_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 126 2
      (.inr (.inl 1)) = 2146516339 := by
  unfold sparseObservation
  change (pw 507 - 7^(2+1)*pw 504) - (pw 3 - 7^(2+1)*pw 0) = 2146516339
  rw [pw_0507, pw_0504, pw3, pw0]
  decide
#print axioms point1_d126_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 132 (direction (127,1)). -/
theorem point1_d127_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 127 0
      (.inr (.inl 1)) = 2147456230 := by
  unfold sparseObservation
  change (pw 509 - 7^(0+1)*pw 508) - (pw 1 - 7^(0+1)*pw 0) = 2147456230
  rw [pw_0509, pw_0508, pw_0001, pw0]
  decide
#print axioms point1_d127_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 134 (direction (156,2)). -/
theorem point1_d156_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 156 1
      (.inr (.inl 1)) = 136320 := by
  unfold sparseObservation
  change (pw 626 - 7^(1+1)*pw 624) - (pw 2 - 7^(1+1)*pw 0) = 136320
  rw [pw_0626, pw_0624, pw_0002, pw0]
  decide
#print axioms point1_d156_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 135 (direction (157,1)). -/
theorem point1_d157_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 157 0
      (.inr (.inl 1)) = 48534 := by
  unfold sparseObservation
  change (pw 629 - 7^(0+1)*pw 628) - (pw 1 - 7^(0+1)*pw 0) = 48534
  rw [pw_0629, pw_0628, pw_0001, pw0]
  decide
#print axioms point1_d157_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 136 (direction (157,2)). -/
theorem point1_d157_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 157 1
      (.inr (.inl 1)) = 330870 := by
  unfold sparseObservation
  change (pw 630 - 7^(1+1)*pw 628) - (pw 2 - 7^(1+1)*pw 0) = 330870
  rw [pw_0630, pw_0628, pw_0002, pw0]
  decide
#print axioms point1_d157_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 137 (direction (158,1)). -/
theorem point1_d158_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 158 0
      (.inr (.inl 1)) = 48564 := by
  unfold sparseObservation
  change (pw 633 - 7^(0+1)*pw 632) - (pw 1 - 7^(0+1)*pw 0) = 48564
  rw [pw_0633, pw_0632, pw_0001, pw0]
  decide
#print axioms point1_d158_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 138 (direction (158,2)). -/
theorem point1_d158_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 158 1
      (.inr (.inl 1)) = 330768 := by
  unfold sparseObservation
  change (pw 634 - 7^(1+1)*pw 632) - (pw 2 - 7^(1+1)*pw 0) = 330768
  rw [pw_0634, pw_0632, pw_0002, pw0]
  decide
#print axioms point1_d158_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 139 (direction (159,1)). -/
theorem point1_d159_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 159 0
      (.inr (.inl 1)) = 1073788565 := by
  unfold sparseObservation
  change (pw 637 - 7^(0+1)*pw 636) - (pw 1 - 7^(0+1)*pw 0) = 1073788565
  rw [pw_0637, pw_0636, pw_0001, pw0]
  decide
#print axioms point1_d159_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 140 (direction (159,2)). -/
theorem point1_d159_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 159 1
      (.inr (.inl 1)) = 1074079301 := by
  unfold sparseObservation
  change (pw 638 - 7^(1+1)*pw 636) - (pw 2 - 7^(1+1)*pw 0) = 1074079301
  rw [pw_0638, pw_0636, pw_0002, pw0]
  decide
#print axioms point1_d159_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 141 (direction (159,3)). -/
theorem point1_d159_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 159 2
      (.inr (.inl 1)) = 539291050 := by
  unfold sparseObservation
  change (pw 639 - 7^(2+1)*pw 636) - (pw 3 - 7^(2+1)*pw 0) = 539291050
  rw [pw_0639, pw_0636, pw3, pw0]
  decide
#print axioms point1_d159_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 142 (direction (188,3)). -/
theorem point1_d188_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 188 2
      (.inr (.inl 1)) = 2147464453 := by
  unfold sparseObservation
  change (pw 755 - 7^(2+1)*pw 752) - (pw 3 - 7^(2+1)*pw 0) = 2147464453
  rw [pw_0755, pw_0752, pw3, pw0]
  decide
#print axioms point1_d188_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 143 (direction (189,1)). -/
theorem point1_d189_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 189 0
      (.inr (.inl 1)) = 2147456860 := by
  unfold sparseObservation
  change (pw 757 - 7^(0+1)*pw 756) - (pw 1 - 7^(0+1)*pw 0) = 2147456860
  rw [pw_0757, pw_0756, pw_0001, pw0]
  decide
#print axioms point1_d189_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 144 (direction (189,3)). -/
theorem point1_d189_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 189 2
      (.inr (.inl 1)) = 1072765175 := by
  unfold sparseObservation
  change (pw 759 - 7^(2+1)*pw 756) - (pw 3 - 7^(2+1)*pw 0) = 1072765175
  rw [pw_0759, pw_0756, pw3, pw0]
  decide
#print axioms point1_d189_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 145 (direction (190,1)). -/
theorem point1_d190_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 190 0
      (.inr (.inl 1)) = 2147456485 := by
  unfold sparseObservation
  change (pw 761 - 7^(0+1)*pw 760) - (pw 1 - 7^(0+1)*pw 0) = 2147456485
  rw [pw_0761, pw_0760, pw_0001, pw0]
  decide
#print axioms point1_d190_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 146 (direction (190,3)). -/
theorem point1_d190_s2 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 190 2
      (.inr (.inl 1)) = 2146508038 := by
  unfold sparseObservation
  change (pw 763 - 7^(2+1)*pw 760) - (pw 3 - 7^(2+1)*pw 0) = 2146508038
  rw [pw_0763, pw_0760, pw3, pw0]
  decide
#print axioms point1_d190_s2
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 147 (direction (191,1)). -/
theorem point1_d191_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 191 0
      (.inr (.inl 1)) = 536866621 := by
  unfold sparseObservation
  change (pw 765 - 7^(0+1)*pw 764) - (pw 1 - 7^(0+1)*pw 0) = 536866621
  rw [pw_0765, pw_0764, pw_0001, pw0]
  decide
#print axioms point1_d191_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 148 (direction (191,2)). -/
theorem point1_d191_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 191 1
      (.inr (.inl 1)) = 536865829 := by
  unfold sparseObservation
  change (pw 766 - 7^(1+1)*pw 764) - (pw 2 - 7^(1+1)*pw 0) = 536865829
  rw [pw_0766, pw_0764, pw_0002, pw0]
  decide
#print axioms point1_d191_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 149 (direction (220,2)). -/
theorem point1_d220_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 220 1
      (.inr (.inl 1)) = 135200 := by
  unfold sparseObservation
  change (pw 882 - 7^(1+1)*pw 880) - (pw 2 - 7^(1+1)*pw 0) = 135200
  rw [pw_0882, pw_0880, pw_0002, pw0]
  decide
#print axioms point1_d220_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 150 (direction (221,1)). -/
theorem point1_d221_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 221 0
      (.inr (.inl 1)) = 49484 := by
  unfold sparseObservation
  change (pw 885 - 7^(0+1)*pw 884) - (pw 1 - 7^(0+1)*pw 0) = 49484
  rw [pw_0885, pw_0884, pw_0001, pw0]
  decide
#print axioms point1_d221_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 151 (direction (221,2)). -/
theorem point1_d221_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 221 1
      (.inr (.inl 1)) = 333580 := by
  unfold sparseObservation
  change (pw 886 - 7^(1+1)*pw 884) - (pw 2 - 7^(1+1)*pw 0) = 333580
  rw [pw_0886, pw_0884, pw_0002, pw0]
  decide
#print axioms point1_d221_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 152 (direction (222,1)). -/
theorem point1_d222_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 222 0
      (.inr (.inl 1)) = 48264 := by
  unfold sparseObservation
  change (pw 889 - 7^(0+1)*pw 888) - (pw 1 - 7^(0+1)*pw 0) = 48264
  rw [pw_0889, pw_0888, pw_0001, pw0]
  decide
#print axioms point1_d222_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 153 (direction (222,2)). -/
theorem point1_d222_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 222 1
      (.inr (.inl 1)) = 332448 := by
  unfold sparseObservation
  change (pw 890 - 7^(1+1)*pw 888) - (pw 2 - 7^(1+1)*pw 0) = 332448
  rw [pw_0890, pw_0888, pw_0002, pw0]
  decide
#print axioms point1_d222_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 154 (direction (223,1)). -/
theorem point1_d223_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 223 0
      (.inr (.inl 1)) = 48759 := by
  unfold sparseObservation
  change (pw 893 - 7^(0+1)*pw 892) - (pw 1 - 7^(0+1)*pw 0) = 48759
  rw [pw_0893, pw_0892, pw_0001, pw0]
  decide
#print axioms point1_d223_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 155 (direction (223,2)). -/
theorem point1_d223_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 223 1
      (.inr (.inl 1)) = 331095 := by
  unfold sparseObservation
  change (pw 894 - 7^(1+1)*pw 892) - (pw 2 - 7^(1+1)*pw 0) = 331095
  rw [pw_0894, pw_0892, pw_0002, pw0]
  decide
#print axioms point1_d223_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 156 (direction (225,1)). -/
theorem point1_d225_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 225 0
      (.inr (.inl 1)) = 49104 := by
  unfold sparseObservation
  change (pw 901 - 7^(0+1)*pw 900) - (pw 1 - 7^(0+1)*pw 0) = 49104
  rw [pw_0901, pw_0900, pw_0001, pw0]
  decide
#print axioms point1_d225_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 157 (direction (225,2)). -/
theorem point1_d225_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 225 1
      (.inr (.inl 1)) = 332496 := by
  unfold sparseObservation
  change (pw 902 - 7^(1+1)*pw 900) - (pw 2 - 7^(1+1)*pw 0) = 332496
  rw [pw_0902, pw_0900, pw_0002, pw0]
  decide
#print axioms point1_d225_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 158 (direction (226,1)). -/
theorem point1_d226_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 226 0
      (.inr (.inl 1)) = 48384 := by
  unfold sparseObservation
  change (pw 905 - 7^(0+1)*pw 904) - (pw 1 - 7^(0+1)*pw 0) = 48384
  rw [pw_0905, pw_0904, pw_0001, pw0]
  decide
#print axioms point1_d226_s0
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 159 (direction (226,2)). -/
theorem point1_d226_s1 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 226 1
      (.inr (.inl 1)) = 331776 := by
  unfold sparseObservation
  change (pw 906 - 7^(1+1)*pw 904) - (pw 2 - 7^(1+1)*pw 0) = 331776
  rw [pw_0906, pw_0904, pw_0002, pw0]
  decide
#print axioms point1_d226_s1
/-- Saved raw matrix SHA-256 91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af: point_1 row 215, raw column 160 (direction (227,1)). -/
theorem point1_d227_s0 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 227 0
      (.inr (.inl 1)) = 48744 := by
  unfold sparseObservation
  change (pw 909 - 7^(0+1)*pw 908) - (pw 1 - 7^(0+1)*pw 0) = 48744
  rw [pw_0909, pw_0908, pw_0001, pw0]
  decide
#print axioms point1_d227_s0
end AspisV8R19.R769Point1SelectedChunk04
