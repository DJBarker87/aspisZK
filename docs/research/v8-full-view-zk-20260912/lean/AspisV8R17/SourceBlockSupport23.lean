import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column31_later : List ℕ := [284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column31_excluded : ∀ r ∈ column31_later,
    ¬evenUnitSupport 115 r ∧ ¬evenUnitSupport 114 r := by decide
theorem column31_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column31_later) :
    sourceChord half (fun i => unitVector 230 i-t*unitVector 228 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column31_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 115 r (by decide) hq,
      sourceChord_even_zero half 114 r (by decide) hb]
  simp
#print axioms column31_excluded
#print axioms column31_zero

def column42_later : List ℕ := [310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column42_excluded : ∀ r ∈ column42_later,
    ¬oddUnitSupport 140 r ∧ ¬evenUnitSupport 140 r := by decide
theorem column42_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column42_later) :
    sourceChord half (fun i => unitVector 281 i-t*unitVector 280 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column42_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 140 r (by decide) hq,
      sourceChord_even_zero half 140 r (by decide) hb]
  simp
#print axioms column42_excluded
#print axioms column42_zero

def column43_later : List ℕ := [310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column43_excluded : ∀ r ∈ column43_later,
    ¬evenUnitSupport 141 r ∧ ¬evenUnitSupport 140 r := by decide
theorem column43_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column43_later) :
    sourceChord half (fun i => unitVector 282 i-t*unitVector 280 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column43_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 141 r (by decide) hq,
      sourceChord_even_zero half 140 r (by decide) hb]
  simp
#print axioms column43_excluded
#print axioms column43_zero

def column48_later : List ℕ := [336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column48_excluded : ∀ r ∈ column48_later,
    ¬oddUnitSupport 153 r ∧ ¬evenUnitSupport 152 r := by decide
theorem column48_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column48_later) :
    sourceChord half (fun i => unitVector 307 i-t*unitVector 304 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column48_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 153 r (by decide) hq,
      sourceChord_even_zero half 152 r (by decide) hb]
  simp
#print axioms column48_excluded
#print axioms column48_zero

def column49_later : List ℕ := [336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column49_excluded : ∀ r ∈ column49_later,
    ¬oddUnitSupport 154 r ∧ ¬evenUnitSupport 154 r := by decide
theorem column49_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column49_later) :
    sourceChord half (fun i => unitVector 309 i-t*unitVector 308 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column49_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 154 r (by decide) hq,
      sourceChord_even_zero half 154 r (by decide) hb]
  simp
#print axioms column49_excluded
#print axioms column49_zero

def column54_later : List ℕ := [362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column54_excluded : ∀ r ∈ column54_later,
    ¬oddUnitSupport 166 r ∧ ¬evenUnitSupport 166 r := by decide
theorem column54_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column54_later) :
    sourceChord half (fun i => unitVector 333 i-t*unitVector 332 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column54_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 166 r (by decide) hq,
      sourceChord_even_zero half 166 r (by decide) hb]
  simp
#print axioms column54_excluded
#print axioms column54_zero

def column55_later : List ℕ := [362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column55_excluded : ∀ r ∈ column55_later,
    ¬evenUnitSupport 167 r ∧ ¬evenUnitSupport 166 r := by decide
theorem column55_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column55_later) :
    sourceChord half (fun i => unitVector 334 i-t*unitVector 332 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column55_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 167 r (by decide) hq,
      sourceChord_even_zero half 166 r (by decide) hb]
  simp
#print axioms column55_excluded
#print axioms column55_zero

def column60_later : List ℕ := [388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column60_excluded : ∀ r ∈ column60_later,
    ¬oddUnitSupport 179 r ∧ ¬evenUnitSupport 178 r := by decide
theorem column60_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column60_later) :
    sourceChord half (fun i => unitVector 359 i-t*unitVector 356 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column60_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 179 r (by decide) hq,
      sourceChord_even_zero half 178 r (by decide) hb]
  simp
#print axioms column60_excluded
#print axioms column60_zero

end AspisV8R17.SourceBlockSupport
