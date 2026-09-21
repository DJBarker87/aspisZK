import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column61_later : List ℕ := [388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column61_excluded : ∀ r ∈ column61_later,
    ¬oddUnitSupport 180 r ∧ ¬evenUnitSupport 180 r := by decide
theorem column61_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column61_later) :
    sourceChord half (fun i => unitVector 361 i-t*unitVector 360 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column61_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 180 r (by decide) hq,
      sourceChord_even_zero half 180 r (by decide) hb]
  simp
#print axioms column61_excluded
#print axioms column61_zero

def column66_later : List ℕ := [451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column66_excluded : ∀ r ∈ column66_later,
    ¬oddUnitSupport 192 r ∧ ¬evenUnitSupport 192 r := by decide
theorem column66_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column66_later) :
    sourceChord half (fun i => unitVector 385 i-t*unitVector 384 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column66_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 192 r (by decide) hq,
      sourceChord_even_zero half 192 r (by decide) hb]
  simp
#print axioms column66_excluded
#print axioms column66_zero

def column67_later : List ℕ := [451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column67_excluded : ∀ r ∈ column67_later,
    ¬evenUnitSupport 193 r ∧ ¬evenUnitSupport 192 r := by decide
theorem column67_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column67_later) :
    sourceChord half (fun i => unitVector 386 i-t*unitVector 384 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column67_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 193 r (by decide) hq,
      sourceChord_even_zero half 192 r (by decide) hb]
  simp
#print axioms column67_excluded
#print axioms column67_zero

def column77_later : List ℕ := [466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column77_excluded : ∀ r ∈ column77_later,
    ¬oddUnitSupport 224 r ∧ ¬evenUnitSupport 224 r := by decide
theorem column77_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column77_later) :
    sourceChord half (fun i => unitVector 449 i-t*unitVector 448 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column77_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 224 r (by decide) hq,
      sourceChord_even_zero half 224 r (by decide) hb]
  simp
#print axioms column77_excluded
#print axioms column77_zero

def column80_later : List ℕ := [1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column80_excluded : ∀ r ∈ column80_later,
    ¬oddUnitSupport 231 r ∧ ¬evenUnitSupport 230 r := by decide
theorem column80_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column80_later) :
    sourceChord half (fun i => unitVector 463 i-t*unitVector 460 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column80_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 231 r (by decide) hq,
      sourceChord_even_zero half 230 r (by decide) hb]
  simp
#print axioms column80_excluded
#print axioms column80_zero

def column81_later : List ℕ := [1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column81_excluded : ∀ r ∈ column81_later,
    ¬oddUnitSupport 232 r ∧ ¬evenUnitSupport 232 r := by decide
theorem column81_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column81_later) :
    sourceChord half (fun i => unitVector 465 i-t*unitVector 464 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column81_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 232 r (by decide) hq,
      sourceChord_even_zero half 232 r (by decide) hb]
  simp
#print axioms column81_excluded
#print axioms column81_zero

def column212_later : List ℕ := [100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column212_excluded : ∀ r ∈ column212_later,
    ¬oddUnitSupport 507 r ∧ ¬evenUnitSupport 506 r := by decide
theorem column212_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column212_later) :
    sourceChord half (fun i => unitVector 1015 i-t*unitVector 1012 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column212_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 507 r (by decide) hq,
      sourceChord_even_zero half 506 r (by decide) hb]
  simp
#print axioms column212_excluded
#print axioms column212_zero

def column213_later : List ℕ := [100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column213_excluded : ∀ r ∈ column213_later,
    ¬oddUnitSupport 508 r ∧ ¬evenUnitSupport 508 r := by decide
theorem column213_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column213_later) :
    sourceChord half (fun i => unitVector 1017 i-t*unitVector 1016 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column213_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 508 r (by decide) hq,
      sourceChord_even_zero half 508 r (by decide) hb]
  simp
#print axioms column213_excluded
#print axioms column213_zero

end AspisV8R17.SourceBlockSupport
