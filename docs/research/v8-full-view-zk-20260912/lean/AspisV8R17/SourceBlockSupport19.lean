import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column28_later : List ℕ := [230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column28_excluded : ∀ r ∈ column28_later,
    ¬evenUnitSupport 109 r ∧ ¬evenUnitSupport 108 r := by decide
theorem column28_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column28_later) :
    sourceChord half (fun i => unitVector 218 i-t*unitVector 216 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column28_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 109 r (by decide) hq,
      sourceChord_even_zero half 108 r (by decide) hb]
  simp
#print axioms column28_excluded
#print axioms column28_zero

def column29_later : List ℕ := [244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column29_excluded : ∀ r ∈ column29_later,
    ¬oddUnitSupport 113 r ∧ ¬evenUnitSupport 112 r := by decide
theorem column29_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column29_later) :
    sourceChord half (fun i => unitVector 227 i-t*unitVector 224 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column29_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 113 r (by decide) hq,
      sourceChord_even_zero half 112 r (by decide) hb]
  simp
#print axioms column29_excluded
#print axioms column29_zero

def column32_later : List ℕ := [269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column32_excluded : ∀ r ∈ column32_later,
    ¬oddUnitSupport 120 r ∧ ¬evenUnitSupport 120 r := by decide
theorem column32_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column32_later) :
    sourceChord half (fun i => unitVector 241 i-t*unitVector 240 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column32_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 120 r (by decide) hq,
      sourceChord_even_zero half 120 r (by decide) hb]
  simp
#print axioms column32_excluded
#print axioms column32_zero

def column33_later : List ℕ := [269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column33_excluded : ∀ r ∈ column33_later,
    ¬evenUnitSupport 121 r ∧ ¬evenUnitSupport 120 r := by decide
theorem column33_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column33_later) :
    sourceChord half (fun i => unitVector 242 i-t*unitVector 240 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column33_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 121 r (by decide) hq,
      sourceChord_even_zero half 120 r (by decide) hb]
  simp
#print axioms column33_excluded
#print axioms column33_zero

def column38_later : List ℕ := [282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column38_excluded : ∀ r ∈ column38_later,
    ¬oddUnitSupport 133 r ∧ ¬evenUnitSupport 132 r := by decide
theorem column38_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column38_later) :
    sourceChord half (fun i => unitVector 267 i-t*unitVector 264 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column38_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 133 r (by decide) hq,
      sourceChord_even_zero half 132 r (by decide) hb]
  simp
#print axioms column38_excluded
#print axioms column38_zero

def column39_later : List ℕ := [282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column39_excluded : ∀ r ∈ column39_later,
    ¬oddUnitSupport 134 r ∧ ¬evenUnitSupport 134 r := by decide
theorem column39_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column39_later) :
    sourceChord half (fun i => unitVector 269 i-t*unitVector 268 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column39_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 134 r (by decide) hq,
      sourceChord_even_zero half 134 r (by decide) hb]
  simp
#print axioms column39_excluded
#print axioms column39_zero

def column40_later : List ℕ := [282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column40_excluded : ∀ r ∈ column40_later,
    ¬evenUnitSupport 135 r ∧ ¬evenUnitSupport 134 r := by decide
theorem column40_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column40_later) :
    sourceChord half (fun i => unitVector 270 i-t*unitVector 268 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column40_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 135 r (by decide) hq,
      sourceChord_even_zero half 134 r (by decide) hb]
  simp
#print axioms column40_excluded
#print axioms column40_zero

def column41_later : List ℕ := [296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column41_excluded : ∀ r ∈ column41_later,
    ¬oddUnitSupport 139 r ∧ ¬evenUnitSupport 138 r := by decide
theorem column41_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column41_later) :
    sourceChord half (fun i => unitVector 279 i-t*unitVector 276 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column41_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 139 r (by decide) hq,
      sourceChord_even_zero half 138 r (by decide) hb]
  simp
#print axioms column41_excluded
#print axioms column41_zero

end AspisV8R17.SourceBlockSupport
