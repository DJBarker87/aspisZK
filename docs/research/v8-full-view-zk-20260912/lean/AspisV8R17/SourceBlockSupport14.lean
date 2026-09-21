import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column191_later : List ℕ := [982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column191_excluded : ∀ r ∈ column191_later,
    ¬oddUnitSupport 487 r ∧ ¬evenUnitSupport 486 r := by decide
theorem column191_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column191_later) :
    sourceChord half (fun i => unitVector 975 i-t*unitVector 972 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column191_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 487 r (by decide) hq,
      sourceChord_even_zero half 486 r (by decide) hb]
  simp
#print axioms column191_excluded
#print axioms column191_zero

def column192_later : List ℕ := [982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column192_excluded : ∀ r ∈ column192_later,
    ¬oddUnitSupport 488 r ∧ ¬evenUnitSupport 488 r := by decide
theorem column192_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column192_later) :
    sourceChord half (fun i => unitVector 977 i-t*unitVector 976 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column192_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 488 r (by decide) hq,
      sourceChord_even_zero half 488 r (by decide) hb]
  simp
#print axioms column192_excluded
#print axioms column192_zero

def column193_later : List ℕ := [986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column193_excluded : ∀ r ∈ column193_later,
    ¬oddUnitSupport 489 r ∧ ¬evenUnitSupport 488 r := by decide
theorem column193_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column193_later) :
    sourceChord half (fun i => unitVector 979 i-t*unitVector 976 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column193_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 489 r (by decide) hq,
      sourceChord_even_zero half 488 r (by decide) hb]
  simp
#print axioms column193_excluded
#print axioms column193_zero

def column194_later : List ℕ := [986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column194_excluded : ∀ r ∈ column194_later,
    ¬oddUnitSupport 490 r ∧ ¬evenUnitSupport 490 r := by decide
theorem column194_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column194_later) :
    sourceChord half (fun i => unitVector 981 i-t*unitVector 980 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column194_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 490 r (by decide) hq,
      sourceChord_even_zero half 490 r (by decide) hb]
  simp
#print axioms column194_excluded
#print axioms column194_zero

def column195_later : List ℕ := [990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column195_excluded : ∀ r ∈ column195_later,
    ¬oddUnitSupport 491 r ∧ ¬evenUnitSupport 490 r := by decide
theorem column195_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column195_later) :
    sourceChord half (fun i => unitVector 983 i-t*unitVector 980 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column195_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 491 r (by decide) hq,
      sourceChord_even_zero half 490 r (by decide) hb]
  simp
#print axioms column195_excluded
#print axioms column195_zero

def column196_later : List ℕ := [990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column196_excluded : ∀ r ∈ column196_later,
    ¬oddUnitSupport 492 r ∧ ¬evenUnitSupport 492 r := by decide
theorem column196_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column196_later) :
    sourceChord half (fun i => unitVector 985 i-t*unitVector 984 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column196_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 492 r (by decide) hq,
      sourceChord_even_zero half 492 r (by decide) hb]
  simp
#print axioms column196_excluded
#print axioms column196_zero

def column197_later : List ℕ := [994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column197_excluded : ∀ r ∈ column197_later,
    ¬oddUnitSupport 493 r ∧ ¬evenUnitSupport 492 r := by decide
theorem column197_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column197_later) :
    sourceChord half (fun i => unitVector 987 i-t*unitVector 984 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column197_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 493 r (by decide) hq,
      sourceChord_even_zero half 492 r (by decide) hb]
  simp
#print axioms column197_excluded
#print axioms column197_zero

def column198_later : List ℕ := [994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column198_excluded : ∀ r ∈ column198_later,
    ¬oddUnitSupport 494 r ∧ ¬evenUnitSupport 494 r := by decide
theorem column198_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column198_later) :
    sourceChord half (fun i => unitVector 989 i-t*unitVector 988 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column198_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 494 r (by decide) hq,
      sourceChord_even_zero half 494 r (by decide) hb]
  simp
#print axioms column198_excluded
#print axioms column198_zero

end AspisV8R17.SourceBlockSupport
