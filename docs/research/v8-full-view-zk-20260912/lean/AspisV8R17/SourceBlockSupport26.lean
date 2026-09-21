import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column72_later : List ℕ := [439, 453, 477, 491, 523]
theorem column72_excluded : ∀ r ∈ column72_later,
    ¬oddUnitSupport 205 r ∧ ¬evenUnitSupport 204 r := by decide
theorem column72_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column72_later) :
    sourceChord half (fun i => unitVector 411 i-t*unitVector 408 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column72_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 205 r (by decide) hq,
      sourceChord_even_zero half 204 r (by decide) hb]
  simp
#print axioms column72_excluded
#print axioms column72_zero

def column76_later : List ℕ := [453, 477, 491, 523]
theorem column76_excluded : ∀ r ∈ column76_later,
    ¬oddUnitSupport 218 r ∧ ¬evenUnitSupport 218 r := by decide
theorem column76_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column76_later) :
    sourceChord half (fun i => unitVector 437 i-t*unitVector 436 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column76_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 218 r (by decide) hq,
      sourceChord_even_zero half 218 r (by decide) hb]
  simp
#print axioms column76_excluded
#print axioms column76_zero

def column78_later : List ℕ := [477, 491, 523]
theorem column78_excluded : ∀ r ∈ column78_later,
    ¬oddUnitSupport 225 r ∧ ¬evenUnitSupport 224 r := by decide
theorem column78_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column78_later) :
    sourceChord half (fun i => unitVector 451 i-t*unitVector 448 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column78_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 225 r (by decide) hq,
      sourceChord_even_zero half 224 r (by decide) hb]
  simp
#print axioms column78_excluded
#print axioms column78_zero

def column82_later : List ℕ := [491, 523]
theorem column82_excluded : ∀ r ∈ column82_later,
    ¬oddUnitSupport 237 r ∧ ¬evenUnitSupport 236 r := by decide
theorem column82_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column82_later) :
    sourceChord half (fun i => unitVector 475 i-t*unitVector 472 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column82_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 237 r (by decide) hq,
      sourceChord_even_zero half 236 r (by decide) hb]
  simp
#print axioms column82_excluded
#print axioms column82_zero

def column83_later : List ℕ := [523]
theorem column83_excluded : ∀ r ∈ column83_later,
    ¬oddUnitSupport 244 r ∧ ¬evenUnitSupport 244 r := by decide
theorem column83_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column83_later) :
    sourceChord half (fun i => unitVector 489 i-t*unitVector 488 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column83_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 244 r (by decide) hq,
      sourceChord_even_zero half 244 r (by decide) hb]
  simp
#print axioms column83_excluded
#print axioms column83_zero

def column88_later : List ℕ := []
theorem column88_excluded : ∀ r ∈ column88_later,
    ¬oddUnitSupport 260 r ∧ ¬evenUnitSupport 260 r := by decide
theorem column88_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column88_later) :
    sourceChord half (fun i => unitVector 521 i-t*unitVector 520 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column88_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 260 r (by decide) hq,
      sourceChord_even_zero half 260 r (by decide) hb]
  simp
#print axioms column88_excluded
#print axioms column88_zero

end AspisV8R17.SourceBlockSupport
