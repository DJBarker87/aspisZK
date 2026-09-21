import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column9_later : List ℕ := [152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column9_excluded : ∀ r ∈ column9_later,
    ¬evenUnitSupport 69 r ∧ ¬evenUnitSupport 68 r := by decide
theorem column9_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column9_later) :
    sourceChord half (fun i => unitVector 138 i-t*unitVector 136 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column9_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 69 r (by decide) hq,
      sourceChord_even_zero half 68 r (by decide) hb]
  simp
#print axioms column9_excluded
#print axioms column9_zero

def column11_later : List ℕ := [165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column11_excluded : ∀ r ∈ column11_later,
    ¬oddUnitSupport 74 r ∧ ¬evenUnitSupport 74 r := by decide
theorem column11_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column11_later) :
    sourceChord half (fun i => unitVector 149 i-t*unitVector 148 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column11_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 74 r (by decide) hq,
      sourceChord_even_zero half 74 r (by decide) hb]
  simp
#print axioms column11_excluded
#print axioms column11_zero

def column14_later : List ℕ := [204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column14_excluded : ∀ r ∈ column14_later,
    ¬oddUnitSupport 81 r ∧ ¬evenUnitSupport 80 r := by decide
theorem column14_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column14_later) :
    sourceChord half (fun i => unitVector 163 i-t*unitVector 160 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column14_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 81 r (by decide) hq,
      sourceChord_even_zero half 80 r (by decide) hb]
  simp
#print axioms column14_excluded
#print axioms column14_zero

def column15_later : List ℕ := [204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column15_excluded : ∀ r ∈ column15_later,
    ¬oddUnitSupport 82 r ∧ ¬evenUnitSupport 82 r := by decide
theorem column15_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column15_later) :
    sourceChord half (fun i => unitVector 165 i-t*unitVector 164 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column15_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 82 r (by decide) hq,
      sourceChord_even_zero half 82 r (by decide) hb]
  simp
#print axioms column15_excluded
#print axioms column15_zero

def column16_later : List ℕ := [204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column16_excluded : ∀ r ∈ column16_later,
    ¬evenUnitSupport 83 r ∧ ¬evenUnitSupport 82 r := by decide
theorem column16_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column16_later) :
    sourceChord half (fun i => unitVector 166 i-t*unitVector 164 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column16_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 83 r (by decide) hq,
      sourceChord_even_zero half 82 r (by decide) hb]
  simp
#print axioms column16_excluded
#print axioms column16_zero

def column23_later : List ℕ := [217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column23_excluded : ∀ r ∈ column23_later,
    ¬oddUnitSupport 100 r ∧ ¬evenUnitSupport 100 r := by decide
theorem column23_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column23_later) :
    sourceChord half (fun i => unitVector 201 i-t*unitVector 200 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column23_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 100 r (by decide) hq,
      sourceChord_even_zero half 100 r (by decide) hb]
  simp
#print axioms column23_excluded
#print axioms column23_zero

def column26_later : List ℕ := [230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column26_excluded : ∀ r ∈ column26_later,
    ¬oddUnitSupport 107 r ∧ ¬evenUnitSupport 106 r := by decide
theorem column26_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column26_later) :
    sourceChord half (fun i => unitVector 215 i-t*unitVector 212 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column26_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 107 r (by decide) hq,
      sourceChord_even_zero half 106 r (by decide) hb]
  simp
#print axioms column26_excluded
#print axioms column26_zero

def column27_later : List ℕ := [230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column27_excluded : ∀ r ∈ column27_later,
    ¬oddUnitSupport 108 r ∧ ¬evenUnitSupport 108 r := by decide
theorem column27_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column27_later) :
    sourceChord half (fun i => unitVector 217 i-t*unitVector 216 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column27_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 108 r (by decide) hq,
      sourceChord_even_zero half 108 r (by decide) hb]
  simp
#print axioms column27_excluded
#print axioms column27_zero

end AspisV8R17.SourceBlockSupport
