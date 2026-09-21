import AspisV8R17.WeightedScatter

/-! Generated arbitrary-field source-model zeros. Stable descending block order.
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Index exclusions only; no evaluated field values or native_decide. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceBlockSupport
def column96_later : List ℕ := [560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column96_excluded : ∀ r ∈ column96_later,
    ¬oddUnitSupport 284 r ∧ ¬evenUnitSupport 284 r := by decide
theorem column96_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column96_later) :
    sourceChord half (fun i => unitVector 569 i-t*unitVector 568 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column96_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 284 r (by decide) hq,
      sourceChord_even_zero half 284 r (by decide) hb]
  simp
#print axioms column96_excluded
#print axioms column96_zero

def column97_later : List ℕ := [560, 588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column97_excluded : ∀ r ∈ column97_later,
    ¬evenUnitSupport 285 r ∧ ¬evenUnitSupport 284 r := by decide
theorem column97_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column97_later) :
    sourceChord half (fun i => unitVector 570 i-t*unitVector 568 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column97_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 285 r (by decide) hq,
      sourceChord_even_zero half 284 r (by decide) hb]
  simp
#print axioms column97_excluded
#print axioms column97_zero

def column95_later : List ℕ := [588, 587, 576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column95_excluded : ∀ r ∈ column95_later,
    ¬oddUnitSupport 278 r ∧ ¬evenUnitSupport 278 r := by decide
theorem column95_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column95_later) :
    sourceChord half (fun i => unitVector 557 i-t*unitVector 556 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column95_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 278 r (by decide) hq,
      sourceChord_even_zero half 278 r (by decide) hb]
  simp
#print axioms column95_excluded
#print axioms column95_zero

def column99_later : List ℕ := [576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column99_excluded : ∀ r ∈ column99_later,
    ¬oddUnitSupport 292 r ∧ ¬evenUnitSupport 292 r := by decide
theorem column99_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column99_later) :
    sourceChord half (fun i => unitVector 585 i-t*unitVector 584 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column99_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 292 r (by decide) hq,
      sourceChord_even_zero half 292 r (by decide) hb]
  simp
#print axioms column99_excluded
#print axioms column99_zero

def column100_later : List ℕ := [576, 604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column100_excluded : ∀ r ∈ column100_later,
    ¬evenUnitSupport 293 r ∧ ¬evenUnitSupport 292 r := by decide
theorem column100_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column100_later) :
    sourceChord half (fun i => unitVector 586 i-t*unitVector 584 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column100_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 293 r (by decide) hq,
      sourceChord_even_zero half 292 r (by decide) hb]
  simp
#print axioms column100_excluded
#print axioms column100_zero

def column98_later : List ℕ := [604, 603, 592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column98_excluded : ∀ r ∈ column98_later,
    ¬oddUnitSupport 286 r ∧ ¬evenUnitSupport 286 r := by decide
theorem column98_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column98_later) :
    sourceChord half (fun i => unitVector 573 i-t*unitVector 572 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column98_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 286 r (by decide) hq,
      sourceChord_even_zero half 286 r (by decide) hb]
  simp
#print axioms column98_excluded
#print axioms column98_zero

def column102_later : List ℕ := [592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column102_excluded : ∀ r ∈ column102_later,
    ¬oddUnitSupport 300 r ∧ ¬evenUnitSupport 300 r := by decide
theorem column102_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column102_later) :
    sourceChord half (fun i => unitVector 601 i-t*unitVector 600 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column102_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_odd_zero half 300 r (by decide) hq,
      sourceChord_even_zero half 300 r (by decide) hb]
  simp
#print axioms column102_excluded
#print axioms column102_zero

def column103_later : List ℕ := [592, 620, 619, 608, 636, 635, 624, 652, 651, 640, 668, 667, 656, 684, 683, 672, 700, 699, 688, 716, 715, 704, 732, 731, 720, 748, 747, 736, 764, 763, 752, 780, 779, 768, 796, 795, 784, 812, 811, 800, 828, 827, 908, 816, 844, 843, 914, 913, 832, 848, 860, 876, 875, 918, 917, 864, 892, 891, 880, 922, 921, 896, 926, 925, 930, 929, 934, 933, 938, 937, 942, 941, 946, 945, 950, 949, 954, 953, 958, 957, 962, 961, 966, 965, 970, 969, 974, 973, 978, 977, 982, 981, 986, 985, 990, 989, 994, 993, 178, 998, 997, 1002, 1001, 193, 258, 257, 1005, 1008, 1006, 321, 323, 322, 1010, 386, 1012, 1014, 113, 115, 114, 140, 139, 152, 165, 167, 166, 204, 217, 219, 218, 230, 244, 243, 269, 271, 270, 282, 296, 295, 308, 334, 348, 347, 360, 373, 375, 374, 400, 399, 425, 427, 426, 464, 1015, 154, 153, 180, 179, 206, 205, 232, 231, 284, 283, 310, 309, 336, 335, 362, 361, 388, 387, 451, 466, 465, 1018, 1017, 100, 101, 141, 245, 297, 349, 401, 412, 413, 439, 453, 477, 491, 523]
theorem column103_excluded : ∀ r ∈ column103_later,
    ¬evenUnitSupport 301 r ∧ ¬evenUnitSupport 300 r := by decide
theorem column103_zero {F : Type*} [CommRing F] (half t a b c : F)
    (r : ℕ) (hr : r ∈ column103_later) :
    sourceChord half (fun i => unitVector 602 i-t*unitVector 600 i) a b c r = 0 := by
  obtain ⟨hq,hb⟩ := column103_excluded r hr
  rw [sourceChord_difference]
  rw [sourceChord_even_zero half 301 r (by decide) hq,
      sourceChord_even_zero half 300 r (by decide) hb]
  simp
#print axioms column103_excluded
#print axioms column103_zero

end AspisV8R17.SourceBlockSupport
