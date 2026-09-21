import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column125_later : List ℕ := [748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column125_excluded : ∀ r ∈ column125_later,
    ¬oddUnitSupport 358 r ∧ ¬evenUnitSupport 358 r := by decide
theorem column125_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column125_later) :
    sourceChord half (fun i => unitVector 717 i-t*unitVector 716 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column125_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 358 r (by decide) hq,
      sourceChord_even_zero half 358 r (by decide) hb]
  simp
#print axioms column125_excluded
#print axioms column125_zero

def column129_later : List ℕ := [736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column129_excluded : ∀ r ∈ column129_later,
    ¬oddUnitSupport 372 r ∧ ¬evenUnitSupport 372 r := by decide
theorem column129_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column129_later) :
    sourceChord half (fun i => unitVector 745 i-t*unitVector 744 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column129_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 372 r (by decide) hq,
      sourceChord_even_zero half 372 r (by decide) hb]
  simp
#print axioms column129_excluded
#print axioms column129_zero

def column130_later : List ℕ := [736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column130_excluded : ∀ r ∈ column130_later,
    ¬evenUnitSupport 373 r ∧ ¬evenUnitSupport 372 r := by decide
theorem column130_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column130_later) :
    sourceChord half (fun i => unitVector 746 i-t*unitVector 744 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column130_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 373 r (by decide) hq,
      sourceChord_even_zero half 372 r (by decide) hb]
  simp
#print axioms column130_excluded
#print axioms column130_zero

def column128_later : List ℕ := [764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column128_excluded : ∀ r ∈ column128_later,
    ¬oddUnitSupport 366 r ∧ ¬evenUnitSupport 366 r := by decide
theorem column128_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column128_later) :
    sourceChord half (fun i => unitVector 733 i-t*unitVector 732 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column128_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 366 r (by decide) hq,
      sourceChord_even_zero half 366 r (by decide) hb]
  simp
#print axioms column128_excluded
#print axioms column128_zero

def column132_later : List ℕ := [752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column132_excluded : ∀ r ∈ column132_later,
    ¬oddUnitSupport 380 r ∧ ¬evenUnitSupport 380 r := by decide
theorem column132_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column132_later) :
    sourceChord half (fun i => unitVector 761 i-t*unitVector 760 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column132_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 380 r (by decide) hq,
      sourceChord_even_zero half 380 r (by decide) hb]
  simp
#print axioms column132_excluded
#print axioms column132_zero

def column133_later : List ℕ := [752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column133_excluded : ∀ r ∈ column133_later,
    ¬evenUnitSupport 381 r ∧ ¬evenUnitSupport 380 r := by decide
theorem column133_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column133_later) :
    sourceChord half (fun i => unitVector 762 i-t*unitVector 760 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column133_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 381 r (by decide) hq,
      sourceChord_even_zero half 380 r (by decide) hb]
  simp
#print axioms column133_excluded
#print axioms column133_zero

def column131_later : List ℕ := [780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column131_excluded : ∀ r ∈ column131_later,
    ¬oddUnitSupport 374 r ∧ ¬evenUnitSupport 374 r := by decide
theorem column131_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column131_later) :
    sourceChord half (fun i => unitVector 749 i-t*unitVector 748 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column131_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 374 r (by decide) hq,
      sourceChord_even_zero half 374 r (by decide) hb]
  simp
#print axioms column131_excluded
#print axioms column131_zero

def column135_later : List ℕ := [768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column135_excluded : ∀ r ∈ column135_later,
    ¬oddUnitSupport 388 r ∧ ¬evenUnitSupport 388 r := by decide
theorem column135_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column135_later) :
    sourceChord half (fun i => unitVector 777 i-t*unitVector 776 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column135_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 388 r (by decide) hq,
      sourceChord_even_zero half 388 r (by decide) hb]
  simp
#print axioms column135_excluded
#print axioms column135_zero

end AspisV8R17.SourceBlockSupport
