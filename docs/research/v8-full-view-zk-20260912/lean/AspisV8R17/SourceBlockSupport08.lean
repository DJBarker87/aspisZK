import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column144_later : List ℕ := [908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column144_excluded : ∀ r ∈ column144_later,
    ¬oddUnitSupport 412 r ∧ ¬evenUnitSupport 412 r := by decide
theorem column144_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column144_later) :
    sourceChord half (fun i => unitVector 825 i-t*unitVector 824 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column144_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 412 r (by decide) hq,
      sourceChord_even_zero half 412 r (by decide) hb]
  simp
#print axioms column144_excluded
#print axioms column144_zero

def column145_later : List ℕ := [908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column145_excluded : ∀ r ∈ column145_later,
    ¬evenUnitSupport 413 r ∧ ¬evenUnitSupport 412 r := by decide
theorem column145_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column145_later) :
    sourceChord half (fun i => unitVector 826 i-t*unitVector 824 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column145_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 413 r (by decide) hq,
      sourceChord_even_zero half 412 r (by decide) hb]
  simp
#print axioms column145_excluded
#print axioms column145_zero

def column158_later : List ℕ := [816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column158_excluded : ∀ r ∈ column158_later,
    ¬oddUnitSupport 452 r ∧ ¬evenUnitSupport 452 r := by decide
theorem column158_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column158_later) :
    sourceChord half (fun i => unitVector 905 i-t*unitVector 904 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column158_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 452 r (by decide) hq,
      sourceChord_even_zero half 452 r (by decide) hb]
  simp
#print axioms column158_excluded
#print axioms column158_zero

def column143_later : List ℕ := [844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column143_excluded : ∀ r ∈ column143_later,
    ¬oddUnitSupport 406 r ∧ ¬evenUnitSupport 406 r := by decide
theorem column143_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column143_later) :
    sourceChord half (fun i => unitVector 813 i-t*unitVector 812 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column143_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 406 r (by decide) hq,
      sourceChord_even_zero half 406 r (by decide) hb]
  simp
#print axioms column143_excluded
#print axioms column143_zero

def column147_later : List ℕ := [914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column147_excluded : ∀ r ∈ column147_later,
    ¬oddUnitSupport 420 r ∧ ¬evenUnitSupport 420 r := by decide
theorem column147_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column147_later) :
    sourceChord half (fun i => unitVector 841 i-t*unitVector 840 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column147_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 420 r (by decide) hq,
      sourceChord_even_zero half 420 r (by decide) hb]
  simp
#print axioms column147_excluded
#print axioms column147_zero

def column148_later : List ℕ := [914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column148_excluded : ∀ r ∈ column148_later,
    ¬evenUnitSupport 421 r ∧ ¬evenUnitSupport 420 r := by decide
theorem column148_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column148_later) :
    sourceChord half (fun i => unitVector 842 i-t*unitVector 840 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column148_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 421 r (by decide) hq,
      sourceChord_even_zero half 420 r (by decide) hb]
  simp
#print axioms column148_excluded
#print axioms column148_zero

def column159_later : List ℕ := [832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column159_excluded : ∀ r ∈ column159_later,
    ¬oddUnitSupport 455 r ∧ ¬evenUnitSupport 454 r := by decide
theorem column159_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column159_later) :
    sourceChord half (fun i => unitVector 911 i-t*unitVector 908 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column159_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 455 r (by decide) hq,
      sourceChord_even_zero half 454 r (by decide) hb]
  simp
#print axioms column159_excluded
#print axioms column159_zero

def column160_later : List ℕ := [832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column160_excluded : ∀ r ∈ column160_later,
    ¬oddUnitSupport 456 r ∧ ¬evenUnitSupport 456 r := by decide
theorem column160_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column160_later) :
    sourceChord half (fun i => unitVector 913 i-t*unitVector 912 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column160_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 456 r (by decide) hq,
      sourceChord_even_zero half 456 r (by decide) hb]
  simp
#print axioms column160_excluded
#print axioms column160_zero

end AspisV8R17.SourceBlockSupport
