import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column36_later : List ℕ := [1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column36_excluded : ∀ r ∈ column36_later,
    ¬oddUnitSupport 127 r ∧ ¬evenUnitSupport 126 r := by decide
theorem column36_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column36_later) :
    sourceChord half (fun i => unitVector 255 i-t*unitVector 252 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column36_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 127 r (by decide) hq,
      sourceChord_even_zero half 126 r (by decide) hb]
  simp
#print axioms column36_excluded
#print axioms column36_zero

def column37_later : List ℕ := [1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column37_excluded : ∀ r ∈ column37_later,
    ¬oddUnitSupport 128 r ∧ ¬evenUnitSupport 128 r := by decide
theorem column37_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column37_later) :
    sourceChord half (fun i => unitVector 257 i-t*unitVector 256 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column37_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 128 r (by decide) hq,
      sourceChord_even_zero half 128 r (by decide) hb]
  simp
#print axioms column37_excluded
#print axioms column37_zero

def column205_later : List ℕ := [321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column205_excluded : ∀ r ∈ column205_later,
    ¬oddUnitSupport 501 r ∧ ¬evenUnitSupport 500 r := by decide
theorem column205_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column205_later) :
    sourceChord half (fun i => unitVector 1003 i-t*unitVector 1000 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column205_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 501 r (by decide) hq,
      sourceChord_even_zero half 500 r (by decide) hb]
  simp
#print axioms column205_excluded
#print axioms column205_zero

def column206_later : List ℕ := [321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column206_excluded : ∀ r ∈ column206_later,
    ¬oddUnitSupport 502 r ∧ ¬evenUnitSupport 502 r := by decide
theorem column206_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column206_later) :
    sourceChord half (fun i => unitVector 1005 i-t*unitVector 1004 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column206_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 502 r (by decide) hq,
      sourceChord_even_zero half 502 r (by decide) hb]
  simp
#print axioms column206_excluded
#print axioms column206_zero

def column207_later : List ℕ := [321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column207_excluded : ∀ r ∈ column207_later,
    ¬evenUnitSupport 503 r ∧ ¬evenUnitSupport 502 r := by decide
theorem column207_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column207_later) :
    sourceChord half (fun i => unitVector 1006 i-t*unitVector 1004 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column207_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 503 r (by decide) hq,
      sourceChord_even_zero half 502 r (by decide) hb]
  simp
#print axioms column207_excluded
#print axioms column207_zero

def column50_later : List ℕ := [1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column50_excluded : ∀ r ∈ column50_later,
    ¬oddUnitSupport 159 r ∧ ¬evenUnitSupport 158 r := by decide
theorem column50_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column50_later) :
    sourceChord half (fun i => unitVector 319 i-t*unitVector 316 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column50_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 159 r (by decide) hq,
      sourceChord_even_zero half 158 r (by decide) hb]
  simp
#print axioms column50_excluded
#print axioms column50_zero

def column51_later : List ℕ := [1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column51_excluded : ∀ r ∈ column51_later,
    ¬oddUnitSupport 160 r ∧ ¬evenUnitSupport 160 r := by decide
theorem column51_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column51_later) :
    sourceChord half (fun i => unitVector 321 i-t*unitVector 320 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column51_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 160 r (by decide) hq,
      sourceChord_even_zero half 160 r (by decide) hb]
  simp
#print axioms column51_excluded
#print axioms column51_zero

def column52_later : List ℕ := [1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column52_excluded : ∀ r ∈ column52_later,
    ¬evenUnitSupport 161 r ∧ ¬evenUnitSupport 160 r := by decide
theorem column52_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column52_later) :
    sourceChord half (fun i => unitVector 322 i-t*unitVector 320 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column52_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 161 r (by decide) hq,
      sourceChord_even_zero half 160 r (by decide) hb]
  simp
#print axioms column52_excluded
#print axioms column52_zero

end AspisV8R17.SourceBlockSupport
