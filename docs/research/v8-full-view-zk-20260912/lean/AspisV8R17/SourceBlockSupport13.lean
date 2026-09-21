import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column183_later : List ℕ := [966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column183_excluded : ∀ r ∈ column183_later,
    ¬oddUnitSupport 479 r ∧ ¬evenUnitSupport 478 r := by decide
theorem column183_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column183_later) :
    sourceChord half (fun i => unitVector 959 i-t*unitVector 956 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column183_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 479 r (by decide) hq,
      sourceChord_even_zero half 478 r (by decide) hb]
  simp
#print axioms column183_excluded
#print axioms column183_zero

def column184_later : List ℕ := [966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column184_excluded : ∀ r ∈ column184_later,
    ¬oddUnitSupport 480 r ∧ ¬evenUnitSupport 480 r := by decide
theorem column184_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column184_later) :
    sourceChord half (fun i => unitVector 961 i-t*unitVector 960 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column184_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 480 r (by decide) hq,
      sourceChord_even_zero half 480 r (by decide) hb]
  simp
#print axioms column184_excluded
#print axioms column184_zero

def column185_later : List ℕ := [970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column185_excluded : ∀ r ∈ column185_later,
    ¬oddUnitSupport 481 r ∧ ¬evenUnitSupport 480 r := by decide
theorem column185_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column185_later) :
    sourceChord half (fun i => unitVector 963 i-t*unitVector 960 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column185_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 481 r (by decide) hq,
      sourceChord_even_zero half 480 r (by decide) hb]
  simp
#print axioms column185_excluded
#print axioms column185_zero

def column186_later : List ℕ := [970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column186_excluded : ∀ r ∈ column186_later,
    ¬oddUnitSupport 482 r ∧ ¬evenUnitSupport 482 r := by decide
theorem column186_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column186_later) :
    sourceChord half (fun i => unitVector 965 i-t*unitVector 964 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column186_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 482 r (by decide) hq,
      sourceChord_even_zero half 482 r (by decide) hb]
  simp
#print axioms column186_excluded
#print axioms column186_zero

def column187_later : List ℕ := [974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column187_excluded : ∀ r ∈ column187_later,
    ¬oddUnitSupport 483 r ∧ ¬evenUnitSupport 482 r := by decide
theorem column187_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column187_later) :
    sourceChord half (fun i => unitVector 967 i-t*unitVector 964 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column187_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 483 r (by decide) hq,
      sourceChord_even_zero half 482 r (by decide) hb]
  simp
#print axioms column187_excluded
#print axioms column187_zero

def column188_later : List ℕ := [974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column188_excluded : ∀ r ∈ column188_later,
    ¬oddUnitSupport 484 r ∧ ¬evenUnitSupport 484 r := by decide
theorem column188_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column188_later) :
    sourceChord half (fun i => unitVector 969 i-t*unitVector 968 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column188_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 484 r (by decide) hq,
      sourceChord_even_zero half 484 r (by decide) hb]
  simp
#print axioms column188_excluded
#print axioms column188_zero

def column189_later : List ℕ := [978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column189_excluded : ∀ r ∈ column189_later,
    ¬oddUnitSupport 485 r ∧ ¬evenUnitSupport 484 r := by decide
theorem column189_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column189_later) :
    sourceChord half (fun i => unitVector 971 i-t*unitVector 968 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column189_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 485 r (by decide) hq,
      sourceChord_even_zero half 484 r (by decide) hb]
  simp
#print axioms column189_excluded
#print axioms column189_zero

def column190_later : List ℕ := [978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column190_excluded : ∀ r ∈ column190_later,
    ¬oddUnitSupport 486 r ∧ ¬evenUnitSupport 486 r := by decide
theorem column190_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column190_later) :
    sourceChord half (fun i => unitVector 973 i-t*unitVector 972 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column190_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 486 r (by decide) hq,
      sourceChord_even_zero half 486 r (by decide) hb]
  simp
#print axioms column190_excluded
#print axioms column190_zero

end AspisV8R17.SourceBlockSupport
