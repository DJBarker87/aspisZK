import PV_B3P_Schedule133
namespace PV_B3P_LegacyValues133
open PV_B3P_Schedule133
set_option autoImplicit false
def spongeFixed : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512]
theorem sponge_eval : ([(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)] : List (Nat × Nat)).map
    (fun (f,t) => link (f*16+11) (t*16)) = spongeFixed := by rfl
#print axioms sponge_eval
def privateFixed : List Link := [path 59 865, path 866 76, path 866 64, path 75 867, path 868 92, path 868 80, path 91 869, path 870 108, path 870 96, path 107 871, path 872 124, path 872 112, path 123 881, path 882 140, path 882 128, path 139 883, path 884 156, path 884 144, path 155 885, path 886 172, path 886 160, path 171 887, path 888 188, path 888 176, path 187 897, path 898 204, path 898 192, path 203 899, path 900 220, path 900 208, path 219 901, path 902 236, path 902 224, path 235 903, path 904 252, path 904 240, path 251 913, path 914 268, path 914 256, path 267 915, path 916 284, path 916 272, path 283 917, path 918 300, path 918 288, path 299 919, path 920 316, path 920 304, path 315 929, path 930 332, path 930 320, path 331 931, path 932 348, path 932 336, path 347 933, path 934 364, path 934 352, path 363 935, path 936 380, path 936 368, path 379 945, path 946 396, path 946 384]
theorem private_eval : (List.range 21).flatMap (fun level =>
    [path ((3+level)*16+11) (legacyAux level),
     path (legacyAux level+1) ((4+level)*16+12),
     path (legacyAux level+1) ((4+level)*16)]) = privateFixed := by rfl
#print axioms private_eval
def appendFixed : List Link := [link 539 556, link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620, link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684, link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748, link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812, link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848]
theorem append_eval : (List.range 20).flatMap (fun level =>
    [link ((33+level)*16+11) ((34+level)*16+12),
     link ((33+level)*16+11) ((34+level)*16)]) = appendFixed := by rfl
#print axioms append_eval
def fixed : List Link := [link 27 32, link 43 48, link 411 416, link 443 448, link 459 464, link 491 496, link 507 512, link 11 28, link 12 412, link 44 428, link 60 428, path 59 865, path 866 76, path 866 64, path 75 867, path 868 92, path 868 80, path 91 869, path 870 108, path 870 96, path 107 871, path 872 124, path 872 112, path 123 881, path 882 140, path 882 128, path 139 883, path 884 156, path 884 144, path 155 885, path 886 172, path 886 160, path 171 887, path 888 188, path 888 176, path 187 897, path 898 204, path 898 192, path 203 899, path 900 220, path 900 208, path 219 901, path 902 236, path 902 224, path 235 903, path 904 252, path 904 240, path 251 913, path 914 268, path 914 256, path 267 915, path 916 284, path 916 272, path 283 917, path 918 300, path 918 288, path 299 919, path 920 316, path 920 304, path 315 929, path 930 332, path 930 320, path 331 931, path 932 348, path 932 336, path 347 933, path 934 364, path 934 352, path 363 935, path 936 380, path 936 368, path 379 945, path 946 396, path 946 384, link 44 960, link 460 962, link 508 964, link 960 966, link 962 966, link 964 967, link 966 967, link 64 969, link 865 969, link 523 970, link 475 540, link 523 540, link 970 528, link 539 556, link 539 544, link 555 572, link 555 560, link 571 588, link 571 576, link 587 604, link 587 592, link 603 620, link 603 608, link 619 636, link 619 624, link 635 652, link 635 640, link 651 668, link 651 656, link 667 684, link 667 672, link 683 700, link 683 688, link 699 716, link 699 704, link 715 732, link 715 720, link 731 748, link 731 736, link 747 764, link 747 752, link 763 780, link 763 768, link 779 796, link 779 784, link 795 812, link 795 800, link 811 828, link 811 816, link 827 844, link 827 832, link 843 860, link 843 848]
theorem legacy_eval : legacyLinks = fixed := by
  unfold legacyLinks
  rw [sponge_eval,private_eval,append_eval]
  rfl
#print axioms legacy_eval
end PV_B3P_LegacyValues133
