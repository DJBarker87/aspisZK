import R1Z.PV_RDB2D_PV_B3P_ForestValues133
namespace PV_B3P_Sorted133
open PV_B3P_Schedule133
set_option autoImplicit false

def endpoints (links : List Link) : List Nat := links.flatMap (fun x => [x.producer,x.consumer])
def chunk0 : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28]
theorem chunk0_eval : endpoints chunk0 = [27, 32, 43, 48, 411, 416, 443, 448, 459, 464, 491, 496, 507, 512, 11, 28] := rfl
#print axioms chunk0_eval
def chunk1 : List Link := [link 12 412, link 44 428, link 60 428, link 44 1008, link 460 1010, link 508 1012, link 1008 1014, link 1010 1014]
theorem chunk1_eval : endpoints chunk1 = [12, 412, 44, 428, 60, 428, 44, 1008, 460, 1010, 508, 1012, 1008, 1014, 1010, 1014] := rfl
#print axioms chunk1_eval
def chunk2 : List Link := [link 1012 1015, link 1014 1015, link 64 1017, link 913 1017, link 523 1018, link 475 540, link 523 540, link 1018 528]
theorem chunk2_eval : endpoints chunk2 = [1012, 1015, 1014, 1015, 64, 1017, 913, 1017, 523, 1018, 475, 540, 523, 540, 1018, 528] := rfl
#print axioms chunk2_eval
def chunk3 : List Link := [link 539 556, link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592]
theorem chunk3_eval : endpoints chunk3 = [539, 556, 539, 544, 555, 572, 555, 560, 571, 588, 571, 576, 587, 604, 587, 592] := rfl
#print axioms chunk3_eval
def chunk4 : List Link := [link 603 620, link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656]
theorem chunk4_eval : endpoints chunk4 = [603, 620, 603, 608, 619, 636, 619, 624, 635, 652, 635, 640, 651, 668, 651, 656] := rfl
#print axioms chunk4_eval
def chunk5 : List Link := [link 667 684, link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720]
theorem chunk5_eval : endpoints chunk5 = [667, 684, 667, 672, 683, 700, 683, 688, 699, 716, 699, 704, 715, 732, 715, 720] := rfl
#print axioms chunk5_eval
def chunk6 : List Link := [link 731 748, link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784]
theorem chunk6_eval : endpoints chunk6 = [731, 748, 731, 736, 747, 764, 747, 752, 763, 780, 763, 768, 779, 796, 779, 784] := rfl
#print axioms chunk6_eval
def chunk7 : List Link := [link 795 812, link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848]
theorem chunk7_eval : endpoints chunk7 = [795, 812, 795, 800, 811, 828, 811, 816, 827, 844, 827, 832, 843, 860, 843, 848] := rfl
#print axioms chunk7_eval
def chunk8 : List Link := [path 59 913, path 914 76, path 914 64, path 75 917, path 918 92, path 918 80, path 91 921, path 922 108]
theorem chunk8_eval : endpoints chunk8 = [59, 913, 914, 76, 914, 64, 75, 917, 918, 92, 918, 80, 91, 921, 922, 108] := rfl
#print axioms chunk8_eval
def chunk9 : List Link := [path 922 96, path 107 925, path 926 124, path 926 112, path 123 929, path 930 140, path 930 128, path 139 933]
theorem chunk9_eval : endpoints chunk9 = [922, 96, 107, 925, 926, 124, 926, 112, 123, 929, 930, 140, 930, 128, 139, 933] := rfl
#print axioms chunk9_eval
def chunk10 : List Link := [path 934 156, path 934 144, path 155 937, path 938 172, path 938 160, path 171 941, path 942 188, path 942 176]
theorem chunk10_eval : endpoints chunk10 = [934, 156, 934, 144, 155, 937, 938, 172, 938, 160, 171, 941, 942, 188, 942, 176] := rfl
#print axioms chunk10_eval
def chunk11 : List Link := [path 187 945, path 946 204, path 946 192, path 203 949, path 950 220, path 950 208, path 219 953, path 954 236]
theorem chunk11_eval : endpoints chunk11 = [187, 945, 946, 204, 946, 192, 203, 949, 950, 220, 950, 208, 219, 953, 954, 236] := rfl
#print axioms chunk11_eval
def chunk12 : List Link := [path 954 224, path 235 957, path 958 252, path 958 240, path 251 961, path 962 268, path 962 256, path 267 965]
theorem chunk12_eval : endpoints chunk12 = [954, 224, 235, 957, 958, 252, 958, 240, 251, 961, 962, 268, 962, 256, 267, 965] := rfl
#print axioms chunk12_eval
def chunk13 : List Link := [path 966 284, path 966 272, path 283 969, path 970 300, path 970 288, path 299 973, path 974 316, path 974 304]
theorem chunk13_eval : endpoints chunk13 = [966, 284, 966, 272, 283, 969, 970, 300, 970, 288, 299, 973, 974, 316, 974, 304] := rfl
#print axioms chunk13_eval
def chunk14 : List Link := [path 315 977, path 978 332, path 978 320, path 331 981, path 982 348, path 982 336, path 347 985, path 986 364]
theorem chunk14_eval : endpoints chunk14 = [315, 977, 978, 332, 978, 320, 331, 981, 982, 348, 982, 336, 347, 985, 986, 364] := rfl
#print axioms chunk14_eval
def chunk15 : List Link := [path 986 352, path 363 989, path 990 380, path 990 368, path 379 993, path 994 396, path 994 384, path 395 997]
theorem chunk15_eval : endpoints chunk15 = [986, 352, 363, 989, 990, 380, 990, 368, 379, 993, 994, 396, 994, 384, 395, 997] := rfl
#print axioms chunk15_eval
def chunk16 : List Link := [path 998 876, path 998 864, path 875 1001, path 1002 892, path 1002 880, path 891 1005, path 1006 908, path 1006 896]
theorem chunk16_eval : endpoints chunk16 = [998, 876, 998, 864, 875, 1001, 1002, 892, 1002, 880, 891, 1005, 1006, 908, 1006, 896] := rfl
#print axioms chunk16_eval
def input : List Nat := [27, 32, 43, 48, 411, 416, 443, 448, 459, 464, 491, 496, 507, 512, 11, 28] ++ ([12, 412, 44, 428, 60, 428, 44, 1008, 460, 1010, 508, 1012, 1008, 1014, 1010, 1014] ++ ([1012, 1015, 1014, 1015, 64, 1017, 913, 1017, 523, 1018, 475, 540, 523, 540, 1018, 528] ++ ([539, 556, 539, 544, 555, 572, 555, 560, 571, 588, 571, 576, 587, 604, 587, 592] ++ ([603, 620, 603, 608, 619, 636, 619, 624, 635, 652, 635, 640, 651, 668, 651, 656] ++ ([667, 684, 667, 672, 683, 700, 683, 688, 699, 716, 699, 704, 715, 732, 715, 720] ++ ([731, 748, 731, 736, 747, 764, 747, 752, 763, 780, 763, 768, 779, 796, 779, 784] ++ ([795, 812, 795, 800, 811, 828, 811, 816, 827, 844, 827, 832, 843, 860, 843, 848] ++ ([59, 913, 914, 76, 914, 64, 75, 917, 918, 92, 918, 80, 91, 921, 922, 108] ++ ([922, 96, 107, 925, 926, 124, 926, 112, 123, 929, 930, 140, 930, 128, 139, 933] ++ ([934, 156, 934, 144, 155, 937, 938, 172, 938, 160, 171, 941, 942, 188, 942, 176] ++ ([187, 945, 946, 204, 946, 192, 203, 949, 950, 220, 950, 208, 219, 953, 954, 236] ++ ([954, 224, 235, 957, 958, 252, 958, 240, 251, 961, 962, 268, 962, 256, 267, 965] ++ ([966, 284, 966, 272, 283, 969, 970, 300, 970, 288, 299, 973, 974, 316, 974, 304] ++ ([315, 977, 978, 332, 978, 320, 331, 981, 982, 348, 982, 336, 347, 985, 986, 364] ++ ([986, 352, 363, 989, 990, 380, 990, 368, 379, 993, 994, 396, 994, 384, 395, 997] ++ ([998, 876, 998, 864, 875, 1001, 1002, 892, 1002, 880, 891, 1005, 1006, 908, 1006, 896]))))))))))))))))
def expected : List Nat := [11, 12, 27, 28, 32, 43, 44, 48, 59, 60, 64, 75, 76, 80, 91, 92] ++ ([96, 107, 108, 112, 123, 124, 128, 139, 140, 144, 155, 156, 160, 171, 172, 176] ++ ([187, 188, 192, 203, 204, 208, 219, 220, 224, 235, 236, 240, 251, 252, 256, 267] ++ ([268, 272, 283, 284, 288, 299, 300, 304, 315, 316, 320, 331, 332, 336, 347, 348] ++ ([352, 363, 364, 368, 379, 380, 384, 395, 396, 411, 412, 416, 428, 443, 448, 459] ++ ([460, 464, 475, 491, 496, 507, 508, 512, 523, 528, 539, 540, 544, 555, 556, 560] ++ ([571, 572, 576, 587, 588, 592, 603, 604, 608, 619, 620, 624, 635, 636, 640, 651] ++ ([652, 656, 667, 668, 672, 683, 684, 688, 699, 700, 704, 715, 716, 720, 731, 732] ++ ([736, 747, 748, 752, 763, 764, 768, 779, 780, 784, 795, 796, 800, 811, 812, 816] ++ ([827, 828, 832, 843, 844, 848, 860, 864, 875, 876, 880, 891, 892, 896, 908, 913] ++ ([914, 917, 918, 921, 922, 925, 926, 929, 930, 933, 934, 937, 938, 941, 942, 945] ++ ([946, 949, 950, 953, 954, 957, 958, 961, 962, 965, 966, 969, 970, 973, 974, 977] ++ ([978, 981, 982, 985, 986, 989, 990, 993, 994, 997, 998, 1001, 1002, 1005, 1006, 1008] ++ ([1010, 1012, 1014, 1015, 1017, 1018])))))))))))))
theorem endpoints_eval : endpoints PV_B3P_ForestValues133.fixed = input := by
  have split : PV_B3P_ForestValues133.fixed = chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 := rfl
  rw [split]
  simp only [endpoints,List.flatMap_append]
  change endpoints chunk0 ++ endpoints chunk1 ++ endpoints chunk2 ++ endpoints chunk3 ++ endpoints chunk4 ++ endpoints chunk5 ++ endpoints chunk6 ++ endpoints chunk7 ++ endpoints chunk8 ++ endpoints chunk9 ++ endpoints chunk10 ++ endpoints chunk11 ++ endpoints chunk12 ++ endpoints chunk13 ++ endpoints chunk14 ++ endpoints chunk15 ++ endpoints chunk16 = input
  rw [chunk0_eval,chunk1_eval,chunk2_eval,chunk3_eval,chunk4_eval,chunk5_eval,chunk6_eval,chunk7_eval,chunk8_eval,chunk9_eval,chunk10_eval,chunk11_eval,chunk12_eval,chunk13_eval,chunk14_eval,chunk15_eval,chunk16_eval]
  simp only [List.append_assoc]
  rfl
end PV_B3P_Sorted133
