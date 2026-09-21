import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column199_later : List ℕ := [178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column199_excluded : ∀ r ∈ column199_later,
    ¬oddUnitSupport 495 r ∧ ¬evenUnitSupport 494 r := by decide
theorem column199_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column199_later) :
    sourceChord half (fun i => unitVector 991 i-t*unitVector 988 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column199_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 495 r (by decide) hq,
      sourceChord_even_zero half 494 r (by decide) hb]
  simp
#print axioms column199_excluded
#print axioms column199_zero

def column200_later : List ℕ := [178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column200_excluded : ∀ r ∈ column200_later,
    ¬oddUnitSupport 496 r ∧ ¬evenUnitSupport 496 r := by decide
theorem column200_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column200_later) :
    sourceChord half (fun i => unitVector 993 i-t*unitVector 992 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column200_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 496 r (by decide) hq,
      sourceChord_even_zero half 496 r (by decide) hb]
  simp
#print axioms column200_excluded
#print axioms column200_zero

def column17_later : List ℕ := [998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column17_excluded : ∀ r ∈ column17_later,
    ¬oddUnitSupport 87 r ∧ ¬evenUnitSupport 86 r := by decide
theorem column17_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column17_later) :
    sourceChord half (fun i => unitVector 175 i-t*unitVector 172 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column17_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 87 r (by decide) hq,
      sourceChord_even_zero half 86 r (by decide) hb]
  simp
#print axioms column17_excluded
#print axioms column17_zero

def column201_later : List ℕ := [1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column201_excluded : ∀ r ∈ column201_later,
    ¬oddUnitSupport 497 r ∧ ¬evenUnitSupport 496 r := by decide
theorem column201_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column201_later) :
    sourceChord half (fun i => unitVector 995 i-t*unitVector 992 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column201_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 497 r (by decide) hq,
      sourceChord_even_zero half 496 r (by decide) hb]
  simp
#print axioms column201_excluded
#print axioms column201_zero

def column202_later : List ℕ := [1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column202_excluded : ∀ r ∈ column202_later,
    ¬oddUnitSupport 498 r ∧ ¬evenUnitSupport 498 r := by decide
theorem column202_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column202_later) :
    sourceChord half (fun i => unitVector 997 i-t*unitVector 996 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column202_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 498 r (by decide) hq,
      sourceChord_even_zero half 498 r (by decide) hb]
  simp
#print axioms column202_excluded
#print axioms column202_zero

def column203_later : List ℕ := [193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column203_excluded : ∀ r ∈ column203_later,
    ¬oddUnitSupport 499 r ∧ ¬evenUnitSupport 498 r := by decide
theorem column203_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column203_later) :
    sourceChord half (fun i => unitVector 999 i-t*unitVector 996 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column203_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 499 r (by decide) hq,
      sourceChord_even_zero half 498 r (by decide) hb]
  simp
#print axioms column203_excluded
#print axioms column203_zero

def column204_later : List ℕ := [193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column204_excluded : ∀ r ∈ column204_later,
    ¬oddUnitSupport 500 r ∧ ¬evenUnitSupport 500 r := by decide
theorem column204_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column204_later) :
    sourceChord half (fun i => unitVector 1001 i-t*unitVector 1000 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column204_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 500 r (by decide) hq,
      sourceChord_even_zero half 500 r (by decide) hb]
  simp
#print axioms column204_excluded
#print axioms column204_zero

def column22_later : List ℕ := [258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column22_excluded : ∀ r ∈ column22_later,
    ¬oddUnitSupport 95 r ∧ ¬evenUnitSupport 94 r := by decide
theorem column22_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column22_later) :
    sourceChord half (fun i => unitVector 191 i-t*unitVector 188 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column22_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 95 r (by decide) hq,
      sourceChord_even_zero half 94 r (by decide) hb]
  simp
#print axioms column22_excluded
#print axioms column22_zero

end AspisV8R17.SourceBlockSupport
