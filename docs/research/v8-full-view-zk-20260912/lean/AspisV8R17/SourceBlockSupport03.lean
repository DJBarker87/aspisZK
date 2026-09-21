import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column101_later : List ℕ := [620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column101_excluded : ∀ r ∈ column101_later,
    ¬oddUnitSupport 294 r ∧ ¬evenUnitSupport 294 r := by decide
theorem column101_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column101_later) :
    sourceChord half (fun i => unitVector 589 i-t*unitVector 588 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column101_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 294 r (by decide) hq,
      sourceChord_even_zero half 294 r (by decide) hb]
  simp
#print axioms column101_excluded
#print axioms column101_zero

def column105_later : List ℕ := [608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column105_excluded : ∀ r ∈ column105_later,
    ¬oddUnitSupport 308 r ∧ ¬evenUnitSupport 308 r := by decide
theorem column105_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column105_later) :
    sourceChord half (fun i => unitVector 617 i-t*unitVector 616 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column105_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 308 r (by decide) hq,
      sourceChord_even_zero half 308 r (by decide) hb]
  simp
#print axioms column105_excluded
#print axioms column105_zero

def column106_later : List ℕ := [608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column106_excluded : ∀ r ∈ column106_later,
    ¬evenUnitSupport 309 r ∧ ¬evenUnitSupport 308 r := by decide
theorem column106_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column106_later) :
    sourceChord half (fun i => unitVector 618 i-t*unitVector 616 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column106_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 309 r (by decide) hq,
      sourceChord_even_zero half 308 r (by decide) hb]
  simp
#print axioms column106_excluded
#print axioms column106_zero

def column104_later : List ℕ := [636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column104_excluded : ∀ r ∈ column104_later,
    ¬oddUnitSupport 302 r ∧ ¬evenUnitSupport 302 r := by decide
theorem column104_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column104_later) :
    sourceChord half (fun i => unitVector 605 i-t*unitVector 604 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column104_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 302 r (by decide) hq,
      sourceChord_even_zero half 302 r (by decide) hb]
  simp
#print axioms column104_excluded
#print axioms column104_zero

def column108_later : List ℕ := [624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column108_excluded : ∀ r ∈ column108_later,
    ¬oddUnitSupport 316 r ∧ ¬evenUnitSupport 316 r := by decide
theorem column108_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column108_later) :
    sourceChord half (fun i => unitVector 633 i-t*unitVector 632 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column108_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 316 r (by decide) hq,
      sourceChord_even_zero half 316 r (by decide) hb]
  simp
#print axioms column108_excluded
#print axioms column108_zero

def column109_later : List ℕ := [624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column109_excluded : ∀ r ∈ column109_later,
    ¬evenUnitSupport 317 r ∧ ¬evenUnitSupport 316 r := by decide
theorem column109_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column109_later) :
    sourceChord half (fun i => unitVector 634 i-t*unitVector 632 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column109_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 317 r (by decide) hq,
      sourceChord_even_zero half 316 r (by decide) hb]
  simp
#print axioms column109_excluded
#print axioms column109_zero

def column107_later : List ℕ := [652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column107_excluded : ∀ r ∈ column107_later,
    ¬oddUnitSupport 310 r ∧ ¬evenUnitSupport 310 r := by decide
theorem column107_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column107_later) :
    sourceChord half (fun i => unitVector 621 i-t*unitVector 620 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column107_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 310 r (by decide) hq,
      sourceChord_even_zero half 310 r (by decide) hb]
  simp
#print axioms column107_excluded
#print axioms column107_zero

def column111_later : List ℕ := [640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column111_excluded : ∀ r ∈ column111_later,
    ¬oddUnitSupport 324 r ∧ ¬evenUnitSupport 324 r := by decide
theorem column111_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column111_later) :
    sourceChord half (fun i => unitVector 649 i-t*unitVector 648 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column111_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 324 r (by decide) hq,
      sourceChord_even_zero half 324 r (by decide) hb]
  simp
#print axioms column111_excluded
#print axioms column111_zero

end AspisV8R17.SourceBlockSupport
