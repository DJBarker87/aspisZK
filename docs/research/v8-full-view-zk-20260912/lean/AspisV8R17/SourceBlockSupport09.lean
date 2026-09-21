import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column146_later : List ℕ := [848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column146_excluded : ∀ r ∈ column146_later,
    ¬oddUnitSupport 414 r ∧ ¬evenUnitSupport 414 r := by decide
theorem column146_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column146_later) :
    sourceChord half (fun i => unitVector 829 i-t*unitVector 828 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column146_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 414 r (by decide) hq,
      sourceChord_even_zero half 414 r (by decide) hb]
  simp
#print axioms column146_excluded
#print axioms column146_zero

def column149_later : List ℕ := [860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column149_excluded : ∀ r ∈ column149_later,
    ¬oddUnitSupport 422 r ∧ ¬evenUnitSupport 422 r := by decide
theorem column149_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column149_later) :
    sourceChord half (fun i => unitVector 845 i-t*unitVector 844 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column149_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 422 r (by decide) hq,
      sourceChord_even_zero half 422 r (by decide) hb]
  simp
#print axioms column149_excluded
#print axioms column149_zero

def column150_later : List ℕ := [876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column150_excluded : ∀ r ∈ column150_later,
    ¬oddUnitSupport 428 r ∧ ¬evenUnitSupport 428 r := by decide
theorem column150_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column150_later) :
    sourceChord half (fun i => unitVector 857 i-t*unitVector 856 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column150_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 428 r (by decide) hq,
      sourceChord_even_zero half 428 r (by decide) hb]
  simp
#print axioms column150_excluded
#print axioms column150_zero

def column152_later : List ℕ := [918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column152_excluded : ∀ r ∈ column152_later,
    ¬oddUnitSupport 436 r ∧ ¬evenUnitSupport 436 r := by decide
theorem column152_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column152_later) :
    sourceChord half (fun i => unitVector 873 i-t*unitVector 872 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column152_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 436 r (by decide) hq,
      sourceChord_even_zero half 436 r (by decide) hb]
  simp
#print axioms column152_excluded
#print axioms column152_zero

def column153_later : List ℕ := [918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column153_excluded : ∀ r ∈ column153_later,
    ¬evenUnitSupport 437 r ∧ ¬evenUnitSupport 436 r := by decide
theorem column153_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column153_later) :
    sourceChord half (fun i => unitVector 874 i-t*unitVector 872 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column153_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 437 r (by decide) hq,
      sourceChord_even_zero half 436 r (by decide) hb]
  simp
#print axioms column153_excluded
#print axioms column153_zero

def column161_later : List ℕ := [864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column161_excluded : ∀ r ∈ column161_later,
    ¬oddUnitSupport 457 r ∧ ¬evenUnitSupport 456 r := by decide
theorem column161_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column161_later) :
    sourceChord half (fun i => unitVector 915 i-t*unitVector 912 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column161_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 457 r (by decide) hq,
      sourceChord_even_zero half 456 r (by decide) hb]
  simp
#print axioms column161_excluded
#print axioms column161_zero

def column162_later : List ℕ := [864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column162_excluded : ∀ r ∈ column162_later,
    ¬oddUnitSupport 458 r ∧ ¬evenUnitSupport 458 r := by decide
theorem column162_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column162_later) :
    sourceChord half (fun i => unitVector 917 i-t*unitVector 916 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column162_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 458 r (by decide) hq,
      sourceChord_even_zero half 458 r (by decide) hb]
  simp
#print axioms column162_excluded
#print axioms column162_zero

def column151_later : List ℕ := [892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column151_excluded : ∀ r ∈ column151_later,
    ¬oddUnitSupport 430 r ∧ ¬evenUnitSupport 430 r := by decide
theorem column151_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column151_later) :
    sourceChord half (fun i => unitVector 861 i-t*unitVector 860 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column151_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 430 r (by decide) hq,
      sourceChord_even_zero half 430 r (by decide) hb]
  simp
#print axioms column151_excluded
#print axioms column151_zero

end AspisV8R17.SourceBlockSupport
