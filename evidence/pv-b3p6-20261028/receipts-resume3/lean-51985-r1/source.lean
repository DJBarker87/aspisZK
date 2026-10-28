import PV_B3P_LegacyValues133
namespace PV_B3P_ForestValues133
open PV_B3P_Schedule133 PV_B3P_LegacyValues133
set_option autoImplicit false
def retained : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28, link 12 412, link 44 428, link 60 428, link 44 1008, link 460 1010, link 508 1012, link 1008 1014, link 1010 1014, link 1012 1015, link 1014 1015, link 64 1017, link 913 1017, link 523 1018, link 475 540, link 523 540, link 1018 528, link 539 556, link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620, link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684, link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748, link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812, link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848]
def chunk0 : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28]
theorem chunk0_eval : (chunk0.filter (fun x => !x.path)).map translate = [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28] := rfl
#print axioms chunk0_eval
def chunk1 : List Link := [link 12 412, link 44 428, link 60 428, path 59 865, path 866 76, path 866 64, path 75 867, path 868 92]
theorem chunk1_eval : (chunk1.filter (fun x => !x.path)).map translate = [link 12 412, link 44 428, link 60 428] := rfl
#print axioms chunk1_eval
def chunk2 : List Link := [path 868 80, path 91 869, path 870 108, path 870 96, path 107 871, path 872 124, path 872 112, path 123 881]
theorem chunk2_eval : (chunk2.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk2_eval
def chunk3 : List Link := [path 882 140, path 882 128, path 139 883, path 884 156, path 884 144, path 155 885, path 886 172, path 886 160]
theorem chunk3_eval : (chunk3.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk3_eval
def chunk4 : List Link := [path 171 887, path 888 188, path 888 176, path 187 897, path 898 204, path 898 192, path 203 899, path 900 220]
theorem chunk4_eval : (chunk4.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk4_eval
def chunk5 : List Link := [path 900 208, path 219 901, path 902 236, path 902 224, path 235 903, path 904 252, path 904 240, path 251 913]
theorem chunk5_eval : (chunk5.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk5_eval
def chunk6 : List Link := [path 914 268, path 914 256, path 267 915, path 916 284, path 916 272, path 283 917, path 918 300, path 918 288]
theorem chunk6_eval : (chunk6.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk6_eval
def chunk7 : List Link := [path 299 919, path 920 316, path 920 304, path 315 929, path 930 332, path 930 320, path 331 931, path 932 348]
theorem chunk7_eval : (chunk7.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk7_eval
def chunk8 : List Link := [path 932 336, path 347 933, path 934 364, path 934 352, path 363 935, path 936 380, path 936 368, path 379 945]
theorem chunk8_eval : (chunk8.filter (fun x => !x.path)).map translate = [] := rfl
#print axioms chunk8_eval
def chunk9 : List Link := [path 946 396, path 946 384, link 44 960, link 460 962, link 508 964, link 960 966, link 962 966, link 964 967]
theorem chunk9_eval : (chunk9.filter (fun x => !x.path)).map translate = [link 44 1008, link 460 1010, link 508 1012, link 1008 1014, link 1010 1014, link 1012 1015] := rfl
#print axioms chunk9_eval
def chunk10 : List Link := [link 966 967, link 64 969, link 865 969, link 523 970, link 475 540, link 523 540, link 970 528, link 539 556]
theorem chunk10_eval : (chunk10.filter (fun x => !x.path)).map translate = [link 1014 1015, link 64 1017, link 913 1017, link 523 1018, link 475 540, link 523 540, link 1018 528, link 539 556] := rfl
#print axioms chunk10_eval
def chunk11 : List Link := [link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620]
theorem chunk11_eval : (chunk11.filter (fun x => !x.path)).map translate = [link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620] := rfl
#print axioms chunk11_eval
def chunk12 : List Link := [link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684]
theorem chunk12_eval : (chunk12.filter (fun x => !x.path)).map translate = [link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684] := rfl
#print axioms chunk12_eval
def chunk13 : List Link := [link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748]
theorem chunk13_eval : (chunk13.filter (fun x => !x.path)).map translate = [link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748] := rfl
#print axioms chunk13_eval
def chunk14 : List Link := [link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812]
theorem chunk14_eval : (chunk14.filter (fun x => !x.path)).map translate = [link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812] := rfl
#print axioms chunk14_eval
def chunk15 : List Link := [link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848]
theorem chunk15_eval : (chunk15.filter (fun x => !x.path)).map translate = [link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848] := rfl
#print axioms chunk15_eval
theorem retained_eval : (PV_B3P_LegacyValues133.fixed.filter (fun x => !x.path)).map translate = retained := by
  have split : PV_B3P_LegacyValues133.fixed = chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 := rfl
  rw [split]
  simp only [List.filter_append,List.map_append,chunk0_eval,chunk1_eval,chunk2_eval,chunk3_eval,chunk4_eval,chunk5_eval,chunk6_eval,chunk7_eval,chunk8_eval,chunk9_eval,chunk10_eval,chunk11_eval,chunk12_eval,chunk13_eval,chunk14_eval,chunk15_eval]
  rfl
#print axioms retained_eval
def pathFixed : List Link := [path 59 913, path 914 76, path 914 64, path 75 917, path 918 92, path 918 80, path 91 921, path 922 108, path 922 96, path 107 925, path 926 124, path 926 112, path 123 929, path 930 140, path 930 128, path 139 933, path 934 156, path 934 144, path 155 937, path 938 172, path 938 160, path 171 941, path 942 188, path 942 176, path 187 945, path 946 204, path 946 192, path 203 949, path 950 220, path 950 208, path 219 953, path 954 236, path 954 224, path 235 957, path 958 252, path 958 240, path 251 961, path 962 268, path 962 256, path 267 965, path 966 284, path 966 272, path 283 969, path 970 300, path 970 288, path 299 973, path 974 316, path 974 304, path 315 977, path 978 332, path 978 320, path 331 981, path 982 348, path 982 336, path 347 985, path 986 364, path 986 352, path 363 989, path 990 380, path 990 368, path 379 993, path 994 396, path 994 384, path 395 997, path 998 876, path 998 864, path 875 1001, path 1002 892, path 1002 880, path 891 1005, path 1006 908, path 1006 896]
theorem paths_eval : (List.range 24).flatMap (fun level =>
    let previous := if level == 0 then 3 else forestBlock (level-1)
    [path (previous*16+11) (forestAux level),
     path (forestAux level+1) (forestBlock level*16+12),
     path (forestAux level+1) (forestBlock level*16)]) = pathFixed := rfl
#print axioms paths_eval
def fixed : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28, link 12 412, link 44 428, link 60 428, link 44 1008, link 460 1010, link 508 1012, link 1008 1014, link 1010 1014, link 1012 1015, link 1014 1015, link 64 1017, link 913 1017, link 523 1018, link 475 540, link 523 540, link 1018 528, link 539 556, link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620, link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684, link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748, link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812, link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848, path 59 913, path 914 76, path 914 64, path 75 917, path 918 92, path 918 80, path 91 921, path 922 108, path 922 96, path 107 925, path 926 124, path 926 112, path 123 929, path 930 140, path 930 128, path 139 933, path 934 156, path 934 144, path 155 937, path 938 172, path 938 160, path 171 941, path 942 188, path 942 176, path 187 945, path 946 204, path 946 192, path 203 949, path 950 220, path 950 208, path 219 953, path 954 236, path 954 224, path 235 957, path 958 252, path 958 240, path 251 961, path 962 268, path 962 256, path 267 965, path 966 284, path 966 272, path 283 969, path 970 300, path 970 288, path 299 973, path 974 316, path 974 304, path 315 977, path 978 332, path 978 320, path 331 981, path 982 348, path 982 336, path 347 985, path 986 364, path 986 352, path 363 989, path 990 380, path 990 368, path 379 993, path 994 396, path 994 384, path 395 997, path 998 876, path 998 864, path 875 1001, path 1002 892, path 1002 880, path 891 1005, path 1006 908, path 1006 896]
theorem forest_eval : forestLinks legacyLinks = fixed := by
  rw [PV_B3P_LegacyValues133.legacy_eval]
  unfold forestLinks
  rw [retained_eval,paths_eval]
  rfl
#print axioms forest_eval
end PV_B3P_ForestValues133
