import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column136_later : List ℕ := [768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column136_excluded : ∀ r ∈ column136_later,
    ¬evenUnitSupport 389 r ∧ ¬evenUnitSupport 388 r := by decide
theorem column136_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column136_later) :
    sourceChord half (fun i => unitVector 778 i-t*unitVector 776 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column136_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 389 r (by decide) hq,
      sourceChord_even_zero half 388 r (by decide) hb]
  simp
#print axioms column136_excluded
#print axioms column136_zero

def column134_later : List ℕ := [796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column134_excluded : ∀ r ∈ column134_later,
    ¬oddUnitSupport 382 r ∧ ¬evenUnitSupport 382 r := by decide
theorem column134_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column134_later) :
    sourceChord half (fun i => unitVector 765 i-t*unitVector 764 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column134_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 382 r (by decide) hq,
      sourceChord_even_zero half 382 r (by decide) hb]
  simp
#print axioms column134_excluded
#print axioms column134_zero

def column138_later : List ℕ := [784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column138_excluded : ∀ r ∈ column138_later,
    ¬oddUnitSupport 396 r ∧ ¬evenUnitSupport 396 r := by decide
theorem column138_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column138_later) :
    sourceChord half (fun i => unitVector 793 i-t*unitVector 792 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column138_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 396 r (by decide) hq,
      sourceChord_even_zero half 396 r (by decide) hb]
  simp
#print axioms column138_excluded
#print axioms column138_zero

def column139_later : List ℕ := [784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column139_excluded : ∀ r ∈ column139_later,
    ¬evenUnitSupport 397 r ∧ ¬evenUnitSupport 396 r := by decide
theorem column139_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column139_later) :
    sourceChord half (fun i => unitVector 794 i-t*unitVector 792 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column139_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 397 r (by decide) hq,
      sourceChord_even_zero half 396 r (by decide) hb]
  simp
#print axioms column139_excluded
#print axioms column139_zero

def column137_later : List ℕ := [812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column137_excluded : ∀ r ∈ column137_later,
    ¬oddUnitSupport 390 r ∧ ¬evenUnitSupport 390 r := by decide
theorem column137_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column137_later) :
    sourceChord half (fun i => unitVector 781 i-t*unitVector 780 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column137_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 390 r (by decide) hq,
      sourceChord_even_zero half 390 r (by decide) hb]
  simp
#print axioms column137_excluded
#print axioms column137_zero

def column141_later : List ℕ := [800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column141_excluded : ∀ r ∈ column141_later,
    ¬oddUnitSupport 404 r ∧ ¬evenUnitSupport 404 r := by decide
theorem column141_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column141_later) :
    sourceChord half (fun i => unitVector 809 i-t*unitVector 808 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column141_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 404 r (by decide) hq,
      sourceChord_even_zero half 404 r (by decide) hb]
  simp
#print axioms column141_excluded
#print axioms column141_zero

def column142_later : List ℕ := [800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column142_excluded : ∀ r ∈ column142_later,
    ¬evenUnitSupport 405 r ∧ ¬evenUnitSupport 404 r := by decide
theorem column142_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column142_later) :
    sourceChord half (fun i => unitVector 810 i-t*unitVector 808 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column142_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 405 r (by decide) hq,
      sourceChord_even_zero half 404 r (by decide) hb]
  simp
#print axioms column142_excluded
#print axioms column142_zero

def column140_later : List ℕ := [828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column140_excluded : ∀ r ∈ column140_later,
    ¬oddUnitSupport 398 r ∧ ¬evenUnitSupport 398 r := by decide
theorem column140_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column140_later) :
    sourceChord half (fun i => unitVector 797 i-t*unitVector 796 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column140_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 398 r (by decide) hq,
      sourceChord_even_zero half 398 r (by decide) hb]
  simp
#print axioms column140_excluded
#print axioms column140_zero

end AspisV8R17.SourceBlockSupport
