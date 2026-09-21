import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column63_later : List ℕ := [400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column63_excluded : ∀ r ∈ column63_later,
    ¬oddUnitSupport 186 r ∧ ¬evenUnitSupport 186 r := by decide
theorem column63_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column63_later) :
    sourceChord half (fun i => unitVector 373 i-t*unitVector 372 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column63_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 186 r (by decide) hq,
      sourceChord_even_zero half 186 r (by decide) hb]
  simp
#print axioms column63_excluded
#print axioms column63_zero

def column64_later : List ℕ := [400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column64_excluded : ∀ r ∈ column64_later,
    ¬evenUnitSupport 187 r ∧ ¬evenUnitSupport 186 r := by decide
theorem column64_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column64_later) :
    sourceChord half (fun i => unitVector 374 i-t*unitVector 372 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column64_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 187 r (by decide) hq,
      sourceChord_even_zero half 186 r (by decide) hb]
  simp
#print axioms column64_excluded
#print axioms column64_zero

def column68_later : List ℕ := [425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column68_excluded : ∀ r ∈ column68_later,
    ¬oddUnitSupport 198 r ∧ ¬evenUnitSupport 198 r := by decide
theorem column68_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column68_later) :
    sourceChord half (fun i => unitVector 397 i-t*unitVector 396 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column68_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 198 r (by decide) hq,
      sourceChord_even_zero half 198 r (by decide) hb]
  simp
#print axioms column68_excluded
#print axioms column68_zero

def column69_later : List ℕ := [425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column69_excluded : ∀ r ∈ column69_later,
    ¬evenUnitSupport 199 r ∧ ¬evenUnitSupport 198 r := by decide
theorem column69_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column69_later) :
    sourceChord half (fun i => unitVector 398 i-t*unitVector 396 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column69_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 199 r (by decide) hq,
      sourceChord_even_zero half 198 r (by decide) hb]
  simp
#print axioms column69_excluded
#print axioms column69_zero

def column73_later : List ℕ := [464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column73_excluded : ∀ r ∈ column73_later,
    ¬oddUnitSupport 211 r ∧ ¬evenUnitSupport 210 r := by decide
theorem column73_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column73_later) :
    sourceChord half (fun i => unitVector 423 i-t*unitVector 420 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column73_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 211 r (by decide) hq,
      sourceChord_even_zero half 210 r (by decide) hb]
  simp
#print axioms column73_excluded
#print axioms column73_zero

def column74_later : List ℕ := [464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column74_excluded : ∀ r ∈ column74_later,
    ¬oddUnitSupport 212 r ∧ ¬evenUnitSupport 212 r := by decide
theorem column74_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column74_later) :
    sourceChord half (fun i => unitVector 425 i-t*unitVector 424 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column74_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 212 r (by decide) hq,
      sourceChord_even_zero half 212 r (by decide) hb]
  simp
#print axioms column74_excluded
#print axioms column74_zero

def column75_later : List ℕ := [464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column75_excluded : ∀ r ∈ column75_later,
    ¬evenUnitSupport 213 r ∧ ¬evenUnitSupport 212 r := by decide
theorem column75_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column75_later) :
    sourceChord half (fun i => unitVector 426 i-t*unitVector 424 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column75_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 213 r (by decide) hq,
      sourceChord_even_zero half 212 r (by decide) hb]
  simp
#print axioms column75_excluded
#print axioms column75_zero

def column79_later : List ℕ := [1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column79_excluded : ∀ r ∈ column79_later,
    ¬oddUnitSupport 230 r ∧ ¬evenUnitSupport 230 r := by decide
theorem column79_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column79_later) :
    sourceChord half (fun i => unitVector 461 i-t*unitVector 460 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column79_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 230 r (by decide) hq,
      sourceChord_even_zero half 230 r (by decide) hb]
  simp
#print axioms column79_excluded
#print axioms column79_zero

end AspisV8R17.SourceBlockSupport
