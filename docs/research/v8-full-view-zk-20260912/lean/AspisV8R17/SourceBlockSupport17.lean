import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column208_later : List ℕ := [386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column208_excluded : ∀ r ∈ column208_later,
    ¬oddUnitSupport 503 r ∧ ¬evenUnitSupport 502 r := by decide
theorem column208_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column208_later) :
    sourceChord half (fun i => unitVector 1007 i-t*unitVector 1004 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column208_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 503 r (by decide) hq,
      sourceChord_even_zero half 502 r (by decide) hb]
  simp
#print axioms column208_excluded
#print axioms column208_zero

def column65_later : List ℕ := [1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column65_excluded : ∀ r ∈ column65_later,
    ¬oddUnitSupport 191 r ∧ ¬evenUnitSupport 190 r := by decide
theorem column65_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column65_later) :
    sourceChord half (fun i => unitVector 383 i-t*unitVector 380 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column65_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 191 r (by decide) hq,
      sourceChord_even_zero half 190 r (by decide) hb]
  simp
#print axioms column65_excluded
#print axioms column65_zero

def column209_later : List ℕ := [1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column209_excluded : ∀ r ∈ column209_later,
    ¬oddUnitSupport 504 r ∧ ¬evenUnitSupport 504 r := by decide
theorem column209_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column209_later) :
    sourceChord half (fun i => unitVector 1009 i-t*unitVector 1008 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column209_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 504 r (by decide) hq,
      sourceChord_even_zero half 504 r (by decide) hb]
  simp
#print axioms column209_excluded
#print axioms column209_zero

def column210_later : List ℕ := [113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column210_excluded : ∀ r ∈ column210_later,
    ¬oddUnitSupport 505 r ∧ ¬evenUnitSupport 504 r := by decide
theorem column210_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column210_later) :
    sourceChord half (fun i => unitVector 1011 i-t*unitVector 1008 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column210_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 505 r (by decide) hq,
      sourceChord_even_zero half 504 r (by decide) hb]
  simp
#print axioms column210_excluded
#print axioms column210_zero

def column2_later : List ℕ := [140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column2_excluded : ∀ r ∈ column2_later,
    ¬oddUnitSupport 55 r ∧ ¬evenUnitSupport 54 r := by decide
theorem column2_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column2_later) :
    sourceChord half (fun i => unitVector 111 i-t*unitVector 108 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column2_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 55 r (by decide) hq,
      sourceChord_even_zero half 54 r (by decide) hb]
  simp
#print axioms column2_excluded
#print axioms column2_zero

def column3_later : List ℕ := [140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column3_excluded : ∀ r ∈ column3_later,
    ¬oddUnitSupport 56 r ∧ ¬evenUnitSupport 56 r := by decide
theorem column3_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column3_later) :
    sourceChord half (fun i => unitVector 113 i-t*unitVector 112 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column3_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 56 r (by decide) hq,
      sourceChord_even_zero half 56 r (by decide) hb]
  simp
#print axioms column3_excluded
#print axioms column3_zero

def column4_later : List ℕ := [140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column4_excluded : ∀ r ∈ column4_later,
    ¬evenUnitSupport 57 r ∧ ¬evenUnitSupport 56 r := by decide
theorem column4_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column4_later) :
    sourceChord half (fun i => unitVector 114 i-t*unitVector 112 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column4_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 57 r (by decide) hq,
      sourceChord_even_zero half 56 r (by decide) hb]
  simp
#print axioms column4_excluded
#print axioms column4_zero

def column8_later : List ℕ := [152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column8_excluded : ∀ r ∈ column8_later,
    ¬oddUnitSupport 68 r ∧ ¬evenUnitSupport 68 r := by decide
theorem column8_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column8_later) :
    sourceChord half (fun i => unitVector 137 i-t*unitVector 136 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column8_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 68 r (by decide) hq,
      sourceChord_even_zero half 68 r (by decide) hb]
  simp
#print axioms column8_excluded
#print axioms column8_zero

end AspisV8R17.SourceBlockSupport
