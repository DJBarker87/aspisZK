import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column44_later : List ℕ := [308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column44_excluded : ∀ r ∈ column44_later,
    ¬oddUnitSupport 146 r ∧ ¬evenUnitSupport 146 r := by decide
theorem column44_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column44_later) :
    sourceChord half (fun i => unitVector 293 i-t*unitVector 292 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column44_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 146 r (by decide) hq,
      sourceChord_even_zero half 146 r (by decide) hb]
  simp
#print axioms column44_excluded
#print axioms column44_zero

def column45_later : List ℕ := [308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column45_excluded : ∀ r ∈ column45_later,
    ¬evenUnitSupport 147 r ∧ ¬evenUnitSupport 146 r := by decide
theorem column45_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column45_later) :
    sourceChord half (fun i => unitVector 294 i-t*unitVector 292 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column45_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 147 r (by decide) hq,
      sourceChord_even_zero half 146 r (by decide) hb]
  simp
#print axioms column45_excluded
#print axioms column45_zero

def column47_later : List ℕ := [334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column47_excluded : ∀ r ∈ column47_later,
    ¬oddUnitSupport 152 r ∧ ¬evenUnitSupport 152 r := by decide
theorem column47_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column47_later) :
    sourceChord half (fun i => unitVector 305 i-t*unitVector 304 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column47_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 152 r (by decide) hq,
      sourceChord_even_zero half 152 r (by decide) hb]
  simp
#print axioms column47_excluded
#print axioms column47_zero

def column53_later : List ℕ := [348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column53_excluded : ∀ r ∈ column53_later,
    ¬oddUnitSupport 165 r ∧ ¬evenUnitSupport 164 r := by decide
theorem column53_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column53_later) :
    sourceChord half (fun i => unitVector 331 i-t*unitVector 328 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column53_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 165 r (by decide) hq,
      sourceChord_even_zero half 164 r (by decide) hb]
  simp
#print axioms column53_excluded
#print axioms column53_zero

def column56_later : List ℕ := [360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column56_excluded : ∀ r ∈ column56_later,
    ¬oddUnitSupport 172 r ∧ ¬evenUnitSupport 172 r := by decide
theorem column56_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column56_later) :
    sourceChord half (fun i => unitVector 345 i-t*unitVector 344 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column56_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 172 r (by decide) hq,
      sourceChord_even_zero half 172 r (by decide) hb]
  simp
#print axioms column56_excluded
#print axioms column56_zero

def column57_later : List ℕ := [360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column57_excluded : ∀ r ∈ column57_later,
    ¬evenUnitSupport 173 r ∧ ¬evenUnitSupport 172 r := by decide
theorem column57_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column57_later) :
    sourceChord half (fun i => unitVector 346 i-t*unitVector 344 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column57_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 173 r (by decide) hq,
      sourceChord_even_zero half 172 r (by decide) hb]
  simp
#print axioms column57_excluded
#print axioms column57_zero

def column59_later : List ℕ := [373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column59_excluded : ∀ r ∈ column59_later,
    ¬oddUnitSupport 178 r ∧ ¬evenUnitSupport 178 r := by decide
theorem column59_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column59_later) :
    sourceChord half (fun i => unitVector 357 i-t*unitVector 356 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column59_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 178 r (by decide) hq,
      sourceChord_even_zero half 178 r (by decide) hb]
  simp
#print axioms column59_excluded
#print axioms column59_zero

def column62_later : List ℕ := [400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column62_excluded : ∀ r ∈ column62_later,
    ¬oddUnitSupport 185 r ∧ ¬evenUnitSupport 184 r := by decide
theorem column62_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column62_later) :
    sourceChord half (fun i => unitVector 371 i-t*unitVector 368 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column62_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 185 r (by decide) hq,
      sourceChord_even_zero half 184 r (by decide) hb]
  simp
#print axioms column62_excluded
#print axioms column62_zero

end AspisV8R17.SourceBlockSupport
