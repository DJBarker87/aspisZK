import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column112_later : List ℕ := [640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column112_excluded : ∀ r ∈ column112_later,
    ¬evenUnitSupport 325 r ∧ ¬evenUnitSupport 324 r := by decide
theorem column112_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column112_later) :
    sourceChord half (fun i => unitVector 650 i-t*unitVector 648 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column112_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 325 r (by decide) hq,
      sourceChord_even_zero half 324 r (by decide) hb]
  simp
#print axioms column112_excluded
#print axioms column112_zero

def column110_later : List ℕ := [668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column110_excluded : ∀ r ∈ column110_later,
    ¬oddUnitSupport 318 r ∧ ¬evenUnitSupport 318 r := by decide
theorem column110_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column110_later) :
    sourceChord half (fun i => unitVector 637 i-t*unitVector 636 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column110_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 318 r (by decide) hq,
      sourceChord_even_zero half 318 r (by decide) hb]
  simp
#print axioms column110_excluded
#print axioms column110_zero

def column114_later : List ℕ := [656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column114_excluded : ∀ r ∈ column114_later,
    ¬oddUnitSupport 332 r ∧ ¬evenUnitSupport 332 r := by decide
theorem column114_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column114_later) :
    sourceChord half (fun i => unitVector 665 i-t*unitVector 664 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column114_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 332 r (by decide) hq,
      sourceChord_even_zero half 332 r (by decide) hb]
  simp
#print axioms column114_excluded
#print axioms column114_zero

def column115_later : List ℕ := [656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column115_excluded : ∀ r ∈ column115_later,
    ¬evenUnitSupport 333 r ∧ ¬evenUnitSupport 332 r := by decide
theorem column115_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column115_later) :
    sourceChord half (fun i => unitVector 666 i-t*unitVector 664 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column115_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 333 r (by decide) hq,
      sourceChord_even_zero half 332 r (by decide) hb]
  simp
#print axioms column115_excluded
#print axioms column115_zero

def column113_later : List ℕ := [684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column113_excluded : ∀ r ∈ column113_later,
    ¬oddUnitSupport 326 r ∧ ¬evenUnitSupport 326 r := by decide
theorem column113_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column113_later) :
    sourceChord half (fun i => unitVector 653 i-t*unitVector 652 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column113_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 326 r (by decide) hq,
      sourceChord_even_zero half 326 r (by decide) hb]
  simp
#print axioms column113_excluded
#print axioms column113_zero

def column117_later : List ℕ := [672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column117_excluded : ∀ r ∈ column117_later,
    ¬oddUnitSupport 340 r ∧ ¬evenUnitSupport 340 r := by decide
theorem column117_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column117_later) :
    sourceChord half (fun i => unitVector 681 i-t*unitVector 680 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column117_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 340 r (by decide) hq,
      sourceChord_even_zero half 340 r (by decide) hb]
  simp
#print axioms column117_excluded
#print axioms column117_zero

def column118_later : List ℕ := [672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column118_excluded : ∀ r ∈ column118_later,
    ¬evenUnitSupport 341 r ∧ ¬evenUnitSupport 340 r := by decide
theorem column118_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column118_later) :
    sourceChord half (fun i => unitVector 682 i-t*unitVector 680 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column118_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 341 r (by decide) hq,
      sourceChord_even_zero half 340 r (by decide) hb]
  simp
#print axioms column118_excluded
#print axioms column118_zero

def column116_later : List ℕ := [700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column116_excluded : ∀ r ∈ column116_later,
    ¬oddUnitSupport 334 r ∧ ¬evenUnitSupport 334 r := by decide
theorem column116_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column116_later) :
    sourceChord half (fun i => unitVector 669 i-t*unitVector 668 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column116_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 334 r (by decide) hq,
      sourceChord_even_zero half 334 r (by decide) hb]
  simp
#print axioms column116_excluded
#print axioms column116_zero

end AspisV8R17.SourceBlockSupport
