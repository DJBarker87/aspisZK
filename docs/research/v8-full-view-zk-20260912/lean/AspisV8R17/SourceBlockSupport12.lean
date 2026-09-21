import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column175_later : List ℕ := [950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column175_excluded : ∀ r ∈ column175_later,
    ¬oddUnitSupport 471 r ∧ ¬evenUnitSupport 470 r := by decide
theorem column175_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column175_later) :
    sourceChord half (fun i => unitVector 943 i-t*unitVector 940 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column175_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 471 r (by decide) hq,
      sourceChord_even_zero half 470 r (by decide) hb]
  simp
#print axioms column175_excluded
#print axioms column175_zero

def column176_later : List ℕ := [950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column176_excluded : ∀ r ∈ column176_later,
    ¬oddUnitSupport 472 r ∧ ¬evenUnitSupport 472 r := by decide
theorem column176_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column176_later) :
    sourceChord half (fun i => unitVector 945 i-t*unitVector 944 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column176_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 472 r (by decide) hq,
      sourceChord_even_zero half 472 r (by decide) hb]
  simp
#print axioms column176_excluded
#print axioms column176_zero

def column177_later : List ℕ := [954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column177_excluded : ∀ r ∈ column177_later,
    ¬oddUnitSupport 473 r ∧ ¬evenUnitSupport 472 r := by decide
theorem column177_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column177_later) :
    sourceChord half (fun i => unitVector 947 i-t*unitVector 944 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column177_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 473 r (by decide) hq,
      sourceChord_even_zero half 472 r (by decide) hb]
  simp
#print axioms column177_excluded
#print axioms column177_zero

def column178_later : List ℕ := [954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column178_excluded : ∀ r ∈ column178_later,
    ¬oddUnitSupport 474 r ∧ ¬evenUnitSupport 474 r := by decide
theorem column178_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column178_later) :
    sourceChord half (fun i => unitVector 949 i-t*unitVector 948 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column178_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 474 r (by decide) hq,
      sourceChord_even_zero half 474 r (by decide) hb]
  simp
#print axioms column178_excluded
#print axioms column178_zero

def column179_later : List ℕ := [958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column179_excluded : ∀ r ∈ column179_later,
    ¬oddUnitSupport 475 r ∧ ¬evenUnitSupport 474 r := by decide
theorem column179_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column179_later) :
    sourceChord half (fun i => unitVector 951 i-t*unitVector 948 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column179_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 475 r (by decide) hq,
      sourceChord_even_zero half 474 r (by decide) hb]
  simp
#print axioms column179_excluded
#print axioms column179_zero

def column180_later : List ℕ := [958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column180_excluded : ∀ r ∈ column180_later,
    ¬oddUnitSupport 476 r ∧ ¬evenUnitSupport 476 r := by decide
theorem column180_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column180_later) :
    sourceChord half (fun i => unitVector 953 i-t*unitVector 952 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column180_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 476 r (by decide) hq,
      sourceChord_even_zero half 476 r (by decide) hb]
  simp
#print axioms column180_excluded
#print axioms column180_zero

def column181_later : List ℕ := [962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column181_excluded : ∀ r ∈ column181_later,
    ¬oddUnitSupport 477 r ∧ ¬evenUnitSupport 476 r := by decide
theorem column181_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column181_later) :
    sourceChord half (fun i => unitVector 955 i-t*unitVector 952 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column181_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 477 r (by decide) hq,
      sourceChord_even_zero half 476 r (by decide) hb]
  simp
#print axioms column181_excluded
#print axioms column181_zero

def column182_later : List ℕ := [962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column182_excluded : ∀ r ∈ column182_later,
    ¬oddUnitSupport 478 r ∧ ¬evenUnitSupport 478 r := by decide
theorem column182_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column182_later) :
    sourceChord half (fun i => unitVector 957 i-t*unitVector 956 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column182_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 478 r (by decide) hq,
      sourceChord_even_zero half 478 r (by decide) hb]
  simp
#print axioms column182_excluded
#print axioms column182_zero

end AspisV8R17.SourceBlockSupport
