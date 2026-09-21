import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column211_later : List ℕ := [154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column211_excluded : ∀ r ∈ column211_later,
    ¬oddUnitSupport 506 r ∧ ¬evenUnitSupport 506 r := by decide
theorem column211_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column211_later) :
    sourceChord half (fun i => unitVector 1013 i-t*unitVector 1012 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column211_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 506 r (by decide) hq,
      sourceChord_even_zero half 506 r (by decide) hb]
  simp
#print axioms column211_excluded
#print axioms column211_zero

def column12_later : List ℕ := [180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column12_excluded : ∀ r ∈ column12_later,
    ¬oddUnitSupport 75 r ∧ ¬evenUnitSupport 74 r := by decide
theorem column12_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column12_later) :
    sourceChord half (fun i => unitVector 151 i-t*unitVector 148 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column12_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 75 r (by decide) hq,
      sourceChord_even_zero half 74 r (by decide) hb]
  simp
#print axioms column12_excluded
#print axioms column12_zero

def column13_later : List ℕ := [180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column13_excluded : ∀ r ∈ column13_later,
    ¬oddUnitSupport 76 r ∧ ¬evenUnitSupport 76 r := by decide
theorem column13_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column13_later) :
    sourceChord half (fun i => unitVector 153 i-t*unitVector 152 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column13_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 76 r (by decide) hq,
      sourceChord_even_zero half 76 r (by decide) hb]
  simp
#print axioms column13_excluded
#print axioms column13_zero

def column18_later : List ℕ := [206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column18_excluded : ∀ r ∈ column18_later,
    ¬oddUnitSupport 88 r ∧ ¬evenUnitSupport 88 r := by decide
theorem column18_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column18_later) :
    sourceChord half (fun i => unitVector 177 i-t*unitVector 176 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column18_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 88 r (by decide) hq,
      sourceChord_even_zero half 88 r (by decide) hb]
  simp
#print axioms column18_excluded
#print axioms column18_zero

def column19_later : List ℕ := [206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column19_excluded : ∀ r ∈ column19_later,
    ¬evenUnitSupport 89 r ∧ ¬evenUnitSupport 88 r := by decide
theorem column19_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column19_later) :
    sourceChord half (fun i => unitVector 178 i-t*unitVector 176 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column19_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 89 r (by decide) hq,
      sourceChord_even_zero half 88 r (by decide) hb]
  simp
#print axioms column19_excluded
#print axioms column19_zero

def column24_later : List ℕ := [232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column24_excluded : ∀ r ∈ column24_later,
    ¬oddUnitSupport 101 r ∧ ¬evenUnitSupport 100 r := by decide
theorem column24_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column24_later) :
    sourceChord half (fun i => unitVector 203 i-t*unitVector 200 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column24_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 101 r (by decide) hq,
      sourceChord_even_zero half 100 r (by decide) hb]
  simp
#print axioms column24_excluded
#print axioms column24_zero

def column25_later : List ℕ := [232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column25_excluded : ∀ r ∈ column25_later,
    ¬oddUnitSupport 102 r ∧ ¬evenUnitSupport 102 r := by decide
theorem column25_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column25_later) :
    sourceChord half (fun i => unitVector 205 i-t*unitVector 204 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column25_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 102 r (by decide) hq,
      sourceChord_even_zero half 102 r (by decide) hb]
  simp
#print axioms column25_excluded
#print axioms column25_zero

def column30_later : List ℕ := [284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column30_excluded : ∀ r ∈ column30_later,
    ¬oddUnitSupport 114 r ∧ ¬evenUnitSupport 114 r := by decide
theorem column30_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column30_later) :
    sourceChord half (fun i => unitVector 229 i-t*unitVector 228 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column30_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 114 r (by decide) hq,
      sourceChord_even_zero half 114 r (by decide) hb]
  simp
#print axioms column30_excluded
#print axioms column30_zero

end AspisV8R17.SourceBlockSupport
