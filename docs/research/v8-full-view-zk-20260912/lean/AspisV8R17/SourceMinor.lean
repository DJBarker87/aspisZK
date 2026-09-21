import AspisV8R17.WeightedScatter
import AspisV8R17.BlockOrdering

/-! Source-shaped minor. Artifact correspondence is explicit, not an extraction theorem.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
-/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor

def sourceRows : List ℕ := [100, 101, 113, 114, 115, 126, 127, 128, 139, 140, 141, 152, 153, 154, 165, 166, 167, 178, 179, 180, 191, 192, 193, 204, 205, 206, 217, 218, 219, 230, 231, 232, 243, 244, 245, 256, 257, 258, 269, 270, 271, 282, 283, 284, 295, 296, 297, 308, 309, 310, 321, 322, 323, 334, 335, 336, 347, 348, 349, 360, 361, 362, 373, 374, 375, 386, 387, 388, 399, 400, 401, 412, 413, 425, 426, 427, 439, 451, 453, 464, 465, 466, 477, 491, 496, 507, 508, 512, 523, 528, 539, 540, 544, 555, 556, 560, 571, 572, 576, 587, 588, 592, 603, 604, 608, 619, 620, 624, 635, 636, 640, 651, 652, 656, 667, 668, 672, 683, 684, 688, 699, 700, 704, 715, 716, 720, 731, 732, 736, 747, 748, 752, 763, 764, 768, 779, 780, 784, 795, 796, 800, 811, 812, 816, 827, 828, 832, 843, 844, 848, 860, 864, 875, 876, 880, 891, 892, 896, 908, 913, 914, 917, 918, 921, 922, 925, 926, 929, 930, 933, 934, 937, 938, 941, 942, 945, 946, 949, 950, 953, 954, 957, 958, 961, 962, 965, 966, 969, 970, 973, 974, 977, 978, 981, 982, 985, 986, 989, 990, 993, 994, 997, 998, 1001, 1002, 1005, 1006, 1008, 1010, 1012, 1014, 1015, 1017, 1018]
def selectedColumns : List ℕ := [6, 8, 17, 18, 19, 26, 27, 28, 36, 37, 38, 45, 47, 48, 56, 57, 58, 65, 66, 67, 75, 76, 77, 84, 86, 87, 95, 96, 97, 104, 105, 106, 114, 115, 116, 123, 125, 126, 134, 135, 136, 143, 144, 145, 153, 154, 155, 162, 164, 165, 173, 174, 175, 182, 183, 184, 192, 193, 194, 201, 203, 204, 212, 213, 214, 221, 222, 223, 231, 232, 233, 240, 242, 251, 252, 253, 261, 270, 272, 279, 281, 282, 290, 300, 303, 312, 313, 315, 324, 327, 336, 337, 339, 348, 349, 351, 360, 361, 363, 372, 373, 375, 384, 385, 387, 396, 397, 399, 408, 409, 411, 420, 421, 423, 432, 433, 435, 444, 445, 447, 456, 457, 459, 468, 469, 471, 480, 481, 483, 492, 493, 495, 504, 505, 507, 516, 517, 519, 528, 529, 531, 540, 541, 543, 552, 553, 555, 564, 565, 567, 576, 579, 588, 589, 591, 600, 601, 603, 612, 617, 618, 620, 621, 623, 624, 626, 627, 629, 630, 632, 633, 635, 636, 638, 639, 641, 642, 644, 645, 647, 648, 650, 651, 653, 654, 656, 657, 659, 660, 662, 663, 665, 666, 668, 669, 671, 672, 674, 675, 677, 678, 680, 681, 683, 684, 686, 687, 688, 689, 690, 692, 693, 695, 696]
def orderedRows : List ℕ := [126, 128, 127, 192, 191, 256, 508, 507, 496, 512, 540, 539, 528, 556, 555, 544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
def orderedColumns : List ℕ := [26, 27, 28, 75, 76, 123, 312, 313, 303, 315, 336, 337, 327, 348, 349, 339, 360, 361, 351, 372, 373, 363, 384, 385, 375, 396, 397, 387, 408, 409, 399, 420, 421, 411, 432, 433, 423, 444, 445, 435, 456, 457, 447, 468, 469, 459, 480, 481, 471, 492, 493, 483, 504, 505, 495, 516, 517, 507, 528, 529, 519, 540, 541, 531, 552, 553, 612, 543, 564, 565, 617, 618, 555, 567, 576, 588, 589, 620, 621, 579, 600, 601, 591, 623, 624, 603, 626, 627, 629, 630, 632, 633, 635, 636, 638, 639, 641, 642, 644, 645, 647, 648, 650, 651, 653, 654, 656, 657, 659, 660, 662, 663, 665, 666, 668, 669, 671, 672, 674, 675, 677, 678, 65, 680, 681, 683, 684, 77, 125, 126, 686, 687, 688, 173, 174, 175, 689, 221, 690, 692, 17, 18, 19, 36, 37, 45, 56, 57, 58, 84, 95, 96, 97, 104, 114, 115, 134, 135, 136, 143, 153, 154, 162, 182, 192, 193, 201, 212, 213, 214, 231, 232, 251, 252, 253, 279, 693, 47, 48, 66, 67, 86, 87, 105, 106, 144, 145, 164, 165, 183, 184, 203, 204, 222, 223, 270, 281, 282, 695, 696, 6, 8, 38, 116, 155, 194, 233, 240, 242, 261, 272, 290, 300, 324]

theorem projected_lookup (xs ys zs : List ℕ)
    (h : zs = xs.map (fun j => ys.getD (j%214) 0))
    (hlen : xs.length = 214) (i : Fin 214) :
    ys.getD (BlockOrdering.indexMap xs i).val 0 = zs.getD i.val 0 := by
  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
  rw [h, List.getD_eq_getElem (xs.map (fun j => ys.getD (j%214) 0)) 0
    (by simpa only [List.length_map] using hi)]
  change ys.getD (xs.getD i.val 0 % 214) 0 = _
  rw [List.getD_eq_getElem xs 0 hi]
  rw [List.getElem_map]

theorem row_map : orderedRows = BlockOrdering.rowOrder.map
    (fun j => sourceRows.getD (j%214) 0) := by decide
theorem column_map : orderedColumns = BlockOrdering.columnOrder.map
    (fun j => selectedColumns.getD (j%214) 0) := by decide
theorem row_projection (i : Fin 214) :
    sourceRows.getD (BlockOrdering.rowPerm i).val 0 = orderedRows.getD i.val 0 :=
  projected_lookup _ _ _ row_map (by decide) i
theorem column_projection (i : Fin 214) :
    selectedColumns.getD (BlockOrdering.columnPerm i).val 0 = orderedColumns.getD i.val 0 :=
  projected_lookup _ _ _ column_map (by decide) i

variable {F : Type*} [CommRing F]
def entry (half alpha a b c : F) (r col : ℕ) : F :=
  let base := 4*(22+col/3)
  let channel := 1+col%3
  sourceChord half (fun i => unitVector (base+channel) i-alpha^channel*unitVector base i) a b c r

def minor (half alpha a b c : F) (i j : Fin 214) : F :=
  entry half alpha a b c (sourceRows.getD i.val 0) (selectedColumns.getD j.val 0)

def orderedMinor (half alpha a b c : F) (i j : Fin 214) : F :=
  minor half alpha a b c (BlockOrdering.rowPerm i) (BlockOrdering.columnPerm j)

theorem orderedMinor_entry (half alpha a b c : F) (i j : Fin 214) :
    orderedMinor half alpha a b c i j =
      entry half alpha a b c (orderedRows.getD i.val 0) (orderedColumns.getD j.val 0) := by
  unfold orderedMinor minor
  rw [row_projection, column_projection]

#print axioms row_projection
#print axioms column_projection
#print axioms orderedMinor_entry
end AspisV8R17.SourceMinor
