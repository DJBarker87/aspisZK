import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column155_later : List ℕ := [880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column155_excluded : ∀ r ∈ column155_later,
    ¬oddUnitSupport 444 r ∧ ¬evenUnitSupport 444 r := by decide
theorem column155_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column155_later) :
    sourceChord half (fun i => unitVector 889 i-t*unitVector 888 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column155_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 444 r (by decide) hq,
      sourceChord_even_zero half 444 r (by decide) hb]
  simp
#print axioms column155_excluded
#print axioms column155_zero

def column156_later : List ℕ := [880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column156_excluded : ∀ r ∈ column156_later,
    ¬evenUnitSupport 445 r ∧ ¬evenUnitSupport 444 r := by decide
theorem column156_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column156_later) :
    sourceChord half (fun i => unitVector 890 i-t*unitVector 888 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column156_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 445 r (by decide) hq,
      sourceChord_even_zero half 444 r (by decide) hb]
  simp
#print axioms column156_excluded
#print axioms column156_zero

def column154_later : List ℕ := [922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column154_excluded : ∀ r ∈ column154_later,
    ¬oddUnitSupport 438 r ∧ ¬evenUnitSupport 438 r := by decide
theorem column154_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column154_later) :
    sourceChord half (fun i => unitVector 877 i-t*unitVector 876 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column154_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 438 r (by decide) hq,
      sourceChord_even_zero half 438 r (by decide) hb]
  simp
#print axioms column154_excluded
#print axioms column154_zero

def column163_later : List ℕ := [896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column163_excluded : ∀ r ∈ column163_later,
    ¬oddUnitSupport 459 r ∧ ¬evenUnitSupport 458 r := by decide
theorem column163_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column163_later) :
    sourceChord half (fun i => unitVector 919 i-t*unitVector 916 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column163_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 459 r (by decide) hq,
      sourceChord_even_zero half 458 r (by decide) hb]
  simp
#print axioms column163_excluded
#print axioms column163_zero

def column164_later : List ℕ := [896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column164_excluded : ∀ r ∈ column164_later,
    ¬oddUnitSupport 460 r ∧ ¬evenUnitSupport 460 r := by decide
theorem column164_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column164_later) :
    sourceChord half (fun i => unitVector 921 i-t*unitVector 920 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column164_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 460 r (by decide) hq,
      sourceChord_even_zero half 460 r (by decide) hb]
  simp
#print axioms column164_excluded
#print axioms column164_zero

def column157_later : List ℕ := [926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column157_excluded : ∀ r ∈ column157_later,
    ¬oddUnitSupport 446 r ∧ ¬evenUnitSupport 446 r := by decide
theorem column157_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column157_later) :
    sourceChord half (fun i => unitVector 893 i-t*unitVector 892 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column157_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 446 r (by decide) hq,
      sourceChord_even_zero half 446 r (by decide) hb]
  simp
#print axioms column157_excluded
#print axioms column157_zero

def column165_later : List ℕ := [930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column165_excluded : ∀ r ∈ column165_later,
    ¬oddUnitSupport 461 r ∧ ¬evenUnitSupport 460 r := by decide
theorem column165_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column165_later) :
    sourceChord half (fun i => unitVector 923 i-t*unitVector 920 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column165_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 461 r (by decide) hq,
      sourceChord_even_zero half 460 r (by decide) hb]
  simp
#print axioms column165_excluded
#print axioms column165_zero

def column166_later : List ℕ := [930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column166_excluded : ∀ r ∈ column166_later,
    ¬oddUnitSupport 462 r ∧ ¬evenUnitSupport 462 r := by decide
theorem column166_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column166_later) :
    sourceChord half (fun i => unitVector 925 i-t*unitVector 924 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column166_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 462 r (by decide) hq,
      sourceChord_even_zero half 462 r (by decide) hb]
  simp
#print axioms column166_excluded
#print axioms column166_zero

end AspisV8R17.SourceBlockSupport
