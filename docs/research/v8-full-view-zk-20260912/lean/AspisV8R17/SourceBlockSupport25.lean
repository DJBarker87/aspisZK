import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column0_later : List ℕ := [101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column0_excluded : ∀ r ∈ column0_later,
    ¬oddUnitSupport 48 r ∧ ¬evenUnitSupport 48 r := by decide
theorem column0_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column0_later) :
    sourceChord half (fun i => unitVector 97 i-t*unitVector 96 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column0_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 48 r (by decide) hq,
      sourceChord_even_zero half 48 r (by decide) hb]
  simp
#print axioms column0_excluded
#print axioms column0_zero

def column1_later : List ℕ := [141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column1_excluded : ∀ r ∈ column1_later,
    ¬oddUnitSupport 49 r ∧ ¬evenUnitSupport 48 r := by decide
theorem column1_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column1_later) :
    sourceChord half (fun i => unitVector 99 i-t*unitVector 96 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column1_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 49 r (by decide) hq,
      sourceChord_even_zero half 48 r (by decide) hb]
  simp
#print axioms column1_excluded
#print axioms column1_zero

def column10_later : List ℕ := [245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column10_excluded : ∀ r ∈ column10_later,
    ¬oddUnitSupport 69 r ∧ ¬evenUnitSupport 68 r := by decide
theorem column10_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column10_later) :
    sourceChord half (fun i => unitVector 139 i-t*unitVector 136 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column10_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 69 r (by decide) hq,
      sourceChord_even_zero half 68 r (by decide) hb]
  simp
#print axioms column10_excluded
#print axioms column10_zero

def column34_later : List ℕ := [297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column34_excluded : ∀ r ∈ column34_later,
    ¬oddUnitSupport 121 r ∧ ¬evenUnitSupport 120 r := by decide
theorem column34_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column34_later) :
    sourceChord half (fun i => unitVector 243 i-t*unitVector 240 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column34_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 121 r (by decide) hq,
      sourceChord_even_zero half 120 r (by decide) hb]
  simp
#print axioms column34_excluded
#print axioms column34_zero

def column46_later : List ℕ := [349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column46_excluded : ∀ r ∈ column46_later,
    ¬oddUnitSupport 147 r ∧ ¬evenUnitSupport 146 r := by decide
theorem column46_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column46_later) :
    sourceChord half (fun i => unitVector 295 i-t*unitVector 292 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column46_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 147 r (by decide) hq,
      sourceChord_even_zero half 146 r (by decide) hb]
  simp
#print axioms column46_excluded
#print axioms column46_zero

def column58_later : List ℕ := [401, 412, 413, 439, 453, 477, 491, 523]
theorem column58_excluded : ∀ r ∈ column58_later,
    ¬oddUnitSupport 173 r ∧ ¬evenUnitSupport 172 r := by decide
theorem column58_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column58_later) :
    sourceChord half (fun i => unitVector 347 i-t*unitVector 344 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column58_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 173 r (by decide) hq,
      sourceChord_even_zero half 172 r (by decide) hb]
  simp
#print axioms column58_excluded
#print axioms column58_zero

def column70_later : List ℕ := [412, 413, 439, 453, 477, 491, 523]
theorem column70_excluded : ∀ r ∈ column70_later,
    ¬oddUnitSupport 199 r ∧ ¬evenUnitSupport 198 r := by decide
theorem column70_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column70_later) :
    sourceChord half (fun i => unitVector 399 i-t*unitVector 396 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column70_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 199 r (by decide) hq,
      sourceChord_even_zero half 198 r (by decide) hb]
  simp
#print axioms column70_excluded
#print axioms column70_zero

def column71_later : List ℕ := [413, 439, 453, 477, 491, 523]
theorem column71_excluded : ∀ r ∈ column71_later,
    ¬oddUnitSupport 204 r ∧ ¬evenUnitSupport 204 r := by decide
theorem column71_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column71_later) :
    sourceChord half (fun i => unitVector 409 i-t*unitVector 408 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column71_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 204 r (by decide) hq,
      sourceChord_even_zero half 204 r (by decide) hb]
  simp
#print axioms column71_excluded
#print axioms column71_zero

end AspisV8R17.SourceBlockSupport
