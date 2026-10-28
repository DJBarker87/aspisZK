import PV_B3P_LegacyValues133
namespace PV_B3P_ForestValues133
open PV_B3P_Schedule133 PV_B3P_LegacyValues133
set_option autoImplicit false
def retained : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28, link 12 412, link 44 428, link 60 428, link 44 1008, link 460 1010, link 508 1012, link 1008 1014, link 1010 1014, link 1012 1015, link 1014 1015, link 64 1017, link 913 1017, link 523 1018, link 475 540, link 523 540, link 1018 528, link 539 556, link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620, link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684, link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748, link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812, link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848]
theorem retained_eval :
    (fixed.filter (fun x => !x.path)).map translate = retained := by
  simp only [fixed,List.filter_cons,List.filter_nil,link,path,Bool.not_true,
    Bool.not_false,ite_true,ite_false,List.map_cons,List.map_nil,translate]
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
