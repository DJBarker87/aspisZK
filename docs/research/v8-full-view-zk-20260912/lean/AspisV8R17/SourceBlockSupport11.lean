import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column167_later : List ℕ := [934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column167_excluded : ∀ r ∈ column167_later,
    ¬oddUnitSupport 463 r ∧ ¬evenUnitSupport 462 r := by decide
theorem column167_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column167_later) :
    sourceChord half (fun i => unitVector 927 i-t*unitVector 924 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column167_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 463 r (by decide) hq,
      sourceChord_even_zero half 462 r (by decide) hb]
  simp
#print axioms column167_excluded
#print axioms column167_zero

def column168_later : List ℕ := [934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column168_excluded : ∀ r ∈ column168_later,
    ¬oddUnitSupport 464 r ∧ ¬evenUnitSupport 464 r := by decide
theorem column168_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column168_later) :
    sourceChord half (fun i => unitVector 929 i-t*unitVector 928 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column168_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 464 r (by decide) hq,
      sourceChord_even_zero half 464 r (by decide) hb]
  simp
#print axioms column168_excluded
#print axioms column168_zero

def column169_later : List ℕ := [938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column169_excluded : ∀ r ∈ column169_later,
    ¬oddUnitSupport 465 r ∧ ¬evenUnitSupport 464 r := by decide
theorem column169_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column169_later) :
    sourceChord half (fun i => unitVector 931 i-t*unitVector 928 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column169_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 465 r (by decide) hq,
      sourceChord_even_zero half 464 r (by decide) hb]
  simp
#print axioms column169_excluded
#print axioms column169_zero

def column170_later : List ℕ := [938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column170_excluded : ∀ r ∈ column170_later,
    ¬oddUnitSupport 466 r ∧ ¬evenUnitSupport 466 r := by decide
theorem column170_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column170_later) :
    sourceChord half (fun i => unitVector 933 i-t*unitVector 932 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column170_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 466 r (by decide) hq,
      sourceChord_even_zero half 466 r (by decide) hb]
  simp
#print axioms column170_excluded
#print axioms column170_zero

def column171_later : List ℕ := [942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column171_excluded : ∀ r ∈ column171_later,
    ¬oddUnitSupport 467 r ∧ ¬evenUnitSupport 466 r := by decide
theorem column171_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column171_later) :
    sourceChord half (fun i => unitVector 935 i-t*unitVector 932 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column171_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 467 r (by decide) hq,
      sourceChord_even_zero half 466 r (by decide) hb]
  simp
#print axioms column171_excluded
#print axioms column171_zero

def column172_later : List ℕ := [942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column172_excluded : ∀ r ∈ column172_later,
    ¬oddUnitSupport 468 r ∧ ¬evenUnitSupport 468 r := by decide
theorem column172_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column172_later) :
    sourceChord half (fun i => unitVector 937 i-t*unitVector 936 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column172_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 468 r (by decide) hq,
      sourceChord_even_zero half 468 r (by decide) hb]
  simp
#print axioms column172_excluded
#print axioms column172_zero

def column173_later : List ℕ := [946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column173_excluded : ∀ r ∈ column173_later,
    ¬oddUnitSupport 469 r ∧ ¬evenUnitSupport 468 r := by decide
theorem column173_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column173_later) :
    sourceChord half (fun i => unitVector 939 i-t*unitVector 936 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column173_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 469 r (by decide) hq,
      sourceChord_even_zero half 468 r (by decide) hb]
  simp
#print axioms column173_excluded
#print axioms column173_zero

def column174_later : List ℕ := [946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column174_excluded : ∀ r ∈ column174_later,
    ¬oddUnitSupport 470 r ∧ ¬evenUnitSupport 470 r := by decide
theorem column174_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column174_later) :
    sourceChord half (fun i => unitVector 941 i-t*unitVector 940 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column174_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 470 r (by decide) hq,
      sourceChord_even_zero half 470 r (by decide) hb]
  simp
#print axioms column174_excluded
#print axioms column174_zero

end AspisV8R17.SourceBlockSupport
