import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column84_later : List ℕ := [512, 540, 539, 528, 556, 555, 544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column84_excluded : ∀ r ∈ column84_later,
    ¬oddUnitSupport 246 r ∧ ¬evenUnitSupport 246 r := by decide
theorem column84_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column84_later) :
    sourceChord half (fun i => unitVector 493 i-t*unitVector 492 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column84_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 246 r (by decide) hq,
      sourceChord_even_zero half 246 r (by decide) hb]
  simp
#print axioms column84_excluded
#print axioms column84_zero

def column87_later : List ℕ := [540, 539, 528, 556, 555, 544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column87_excluded : ∀ r ∈ column87_later,
    ¬oddUnitSupport 254 r ∧ ¬evenUnitSupport 254 r := by decide
theorem column87_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column87_later) :
    sourceChord half (fun i => unitVector 509 i-t*unitVector 508 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column87_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 254 r (by decide) hq,
      sourceChord_even_zero half 254 r (by decide) hb]
  simp
#print axioms column87_excluded
#print axioms column87_zero

def column90_later : List ℕ := [528, 556, 555, 544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column90_excluded : ∀ r ∈ column90_later,
    ¬oddUnitSupport 268 r ∧ ¬evenUnitSupport 268 r := by decide
theorem column90_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column90_later) :
    sourceChord half (fun i => unitVector 537 i-t*unitVector 536 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column90_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 268 r (by decide) hq,
      sourceChord_even_zero half 268 r (by decide) hb]
  simp
#print axioms column90_excluded
#print axioms column90_zero

def column91_later : List ℕ := [528, 556, 555, 544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column91_excluded : ∀ r ∈ column91_later,
    ¬evenUnitSupport 269 r ∧ ¬evenUnitSupport 268 r := by decide
theorem column91_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column91_later) :
    sourceChord half (fun i => unitVector 538 i-t*unitVector 536 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column91_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 269 r (by decide) hq,
      sourceChord_even_zero half 268 r (by decide) hb]
  simp
#print axioms column91_excluded
#print axioms column91_zero

def column89_later : List ℕ := [556, 555, 544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column89_excluded : ∀ r ∈ column89_later,
    ¬oddUnitSupport 262 r ∧ ¬evenUnitSupport 262 r := by decide
theorem column89_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column89_later) :
    sourceChord half (fun i => unitVector 525 i-t*unitVector 524 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column89_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 262 r (by decide) hq,
      sourceChord_even_zero half 262 r (by decide) hb]
  simp
#print axioms column89_excluded
#print axioms column89_zero

def column93_later : List ℕ := [544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column93_excluded : ∀ r ∈ column93_later,
    ¬oddUnitSupport 276 r ∧ ¬evenUnitSupport 276 r := by decide
theorem column93_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column93_later) :
    sourceChord half (fun i => unitVector 553 i-t*unitVector 552 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column93_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 276 r (by decide) hq,
      sourceChord_even_zero half 276 r (by decide) hb]
  simp
#print axioms column93_excluded
#print axioms column93_zero

def column94_later : List ℕ := [544, 572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column94_excluded : ∀ r ∈ column94_later,
    ¬evenUnitSupport 277 r ∧ ¬evenUnitSupport 276 r := by decide
theorem column94_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column94_later) :
    sourceChord half (fun i => unitVector 554 i-t*unitVector 552 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column94_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 277 r (by decide) hq,
      sourceChord_even_zero half 276 r (by decide) hb]
  simp
#print axioms column94_excluded
#print axioms column94_zero

def column92_later : List ℕ := [572, 571, 560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column92_excluded : ∀ r ∈ column92_later,
    ¬oddUnitSupport 270 r ∧ ¬evenUnitSupport 270 r := by decide
theorem column92_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column92_later) :
    sourceChord half (fun i => unitVector 541 i-t*unitVector 540 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column92_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 270 r (by decide) hq,
      sourceChord_even_zero half 270 r (by decide) hb]
  simp
#print axioms column92_excluded
#print axioms column92_zero

end AspisV8R17.SourceBlockSupport
