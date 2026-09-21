import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column120_later : List ℕ := [688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column120_excluded : ∀ r ∈ column120_later,
    ¬oddUnitSupport 348 r ∧ ¬evenUnitSupport 348 r := by decide
theorem column120_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column120_later) :
    sourceChord half (fun i => unitVector 697 i-t*unitVector 696 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column120_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 348 r (by decide) hq,
      sourceChord_even_zero half 348 r (by decide) hb]
  simp
#print axioms column120_excluded
#print axioms column120_zero

def column121_later : List ℕ := [688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column121_excluded : ∀ r ∈ column121_later,
    ¬evenUnitSupport 349 r ∧ ¬evenUnitSupport 348 r := by decide
theorem column121_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column121_later) :
    sourceChord half (fun i => unitVector 698 i-t*unitVector 696 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column121_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 349 r (by decide) hq,
      sourceChord_even_zero half 348 r (by decide) hb]
  simp
#print axioms column121_excluded
#print axioms column121_zero

def column119_later : List ℕ := [716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column119_excluded : ∀ r ∈ column119_later,
    ¬oddUnitSupport 342 r ∧ ¬evenUnitSupport 342 r := by decide
theorem column119_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column119_later) :
    sourceChord half (fun i => unitVector 685 i-t*unitVector 684 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column119_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 342 r (by decide) hq,
      sourceChord_even_zero half 342 r (by decide) hb]
  simp
#print axioms column119_excluded
#print axioms column119_zero

def column123_later : List ℕ := [704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column123_excluded : ∀ r ∈ column123_later,
    ¬oddUnitSupport 356 r ∧ ¬evenUnitSupport 356 r := by decide
theorem column123_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column123_later) :
    sourceChord half (fun i => unitVector 713 i-t*unitVector 712 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column123_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 356 r (by decide) hq,
      sourceChord_even_zero half 356 r (by decide) hb]
  simp
#print axioms column123_excluded
#print axioms column123_zero

def column124_later : List ℕ := [704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column124_excluded : ∀ r ∈ column124_later,
    ¬evenUnitSupport 357 r ∧ ¬evenUnitSupport 356 r := by decide
theorem column124_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column124_later) :
    sourceChord half (fun i => unitVector 714 i-t*unitVector 712 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column124_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 357 r (by decide) hq,
      sourceChord_even_zero half 356 r (by decide) hb]
  simp
#print axioms column124_excluded
#print axioms column124_zero

def column122_later : List ℕ := [732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column122_excluded : ∀ r ∈ column122_later,
    ¬oddUnitSupport 350 r ∧ ¬evenUnitSupport 350 r := by decide
theorem column122_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column122_later) :
    sourceChord half (fun i => unitVector 701 i-t*unitVector 700 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column122_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 350 r (by decide) hq,
      sourceChord_even_zero half 350 r (by decide) hb]
  simp
#print axioms column122_excluded
#print axioms column122_zero

def column126_later : List ℕ := [720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column126_excluded : ∀ r ∈ column126_later,
    ¬oddUnitSupport 364 r ∧ ¬evenUnitSupport 364 r := by decide
theorem column126_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column126_later) :
    sourceChord half (fun i => unitVector 729 i-t*unitVector 728 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column126_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 364 r (by decide) hq,
      sourceChord_even_zero half 364 r (by decide) hb]
  simp
#print axioms column126_excluded
#print axioms column126_zero

def column127_later : List ℕ := [720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column127_excluded : ∀ r ∈ column127_later,
    ¬evenUnitSupport 365 r ∧ ¬evenUnitSupport 364 r := by decide
theorem column127_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column127_later) :
    sourceChord half (fun i => unitVector 730 i-t*unitVector 728 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column127_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 365 r (by decide) hq,
      sourceChord_even_zero half 364 r (by decide) hb]
  simp
#print axioms column127_excluded
#print axioms column127_zero

end AspisV8R17.SourceBlockSupport
