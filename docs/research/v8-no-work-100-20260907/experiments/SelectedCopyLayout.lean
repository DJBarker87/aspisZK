import SelectedWeightedCopyRows
import Mathlib.Data.Fin.VecNotation

/-! Literal selected 136-link endpoint layout and the compressed description
of its fourteen contiguous-prefix tuple patterns. The only concrete proof
checks are 272 small endpoint/mask cells and fourteen small range facts,
not field enumeration or a generated circle recurrence.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 150000

namespace AspisV8.SelectedCopyLayout
open AspisV8.SelectedWeightedCopyRows

structure Endpoint where
  row : Fin 1024
  slot : Fin 2
  pattern : Fin 14
  deriving DecidableEq

structure Link where
  producer : Endpoint
  consumer : Endpoint
  deriving DecidableEq

private def link (pr : Fin 1024) (ps : Fin 2) (pp : Fin 14)
    (cr : Fin 1024) (cs : Fin 2) (cp : Fin 14) : Link :=
  ⟨⟨pr,ps,pp⟩,⟨cr,cs,cp⟩⟩

/-- Exact order of COPY_LINKS, retaining slots even for zero-weight links.
Tags and public weight kinds use SelectedWeightedCopyRows' pinned schedule. -/
def sourceLinks : Fin 136 → Link := ![
  link 27 0 0 32 0 0,
  link 43 0 0 48 0 0,
  link 411 0 0 416 0 0,
  link 443 0 0 448 0 0,
  link 459 0 0 464 0 0,
  link 491 0 0 496 0 0,
  link 507 0 0 512 0 0,
  link 11 0 1 28 0 1,
  link 12 0 1 412 0 1,
  link 44 0 2 428 0 3,
  link 60 0 4 428 1 5,
  link 44 1 6 1008 0 7,
  link 460 0 6 1010 0 7,
  link 508 0 6 1012 0 7,
  link 1008 0 7 1014 0 6,
  link 1010 0 7 1014 1 8,
  link 1012 0 7 1015 0 8,
  link 1014 0 9 1015 1 6,
  link 64 0 10 1017 0 11,
  link 913 0 6 1017 1 7,
  link 523 0 1 1018 0 11,
  link 475 0 1 540 0 1,
  link 523 1 1 540 1 1,
  link 1018 0 11 528 0 10,
  link 539 0 1 556 0 1,
  link 539 1 1 544 0 10,
  link 555 0 1 572 0 1,
  link 555 1 1 560 0 10,
  link 571 0 1 588 0 1,
  link 571 1 1 576 0 10,
  link 587 0 1 604 0 1,
  link 587 1 1 592 0 10,
  link 603 0 1 620 0 1,
  link 603 1 1 608 0 10,
  link 619 0 1 636 0 1,
  link 619 1 1 624 0 10,
  link 635 0 1 652 0 1,
  link 635 1 1 640 0 10,
  link 651 0 1 668 0 1,
  link 651 1 1 656 0 10,
  link 667 0 1 684 0 1,
  link 667 1 1 672 0 10,
  link 683 0 1 700 0 1,
  link 683 1 1 688 0 10,
  link 699 0 1 716 0 1,
  link 699 1 1 704 0 10,
  link 715 0 1 732 0 1,
  link 715 1 1 720 0 10,
  link 731 0 1 748 0 1,
  link 731 1 1 736 0 10,
  link 747 0 1 764 0 1,
  link 747 1 1 752 0 10,
  link 763 0 1 780 0 1,
  link 763 1 1 768 0 10,
  link 779 0 1 796 0 1,
  link 779 1 1 784 0 10,
  link 795 0 1 812 0 1,
  link 795 1 1 800 0 10,
  link 811 0 1 828 0 1,
  link 811 1 1 816 0 10,
  link 827 0 1 844 0 1,
  link 827 1 1 832 0 10,
  link 843 0 1 860 0 1,
  link 843 1 1 848 0 10,
  link 59 0 1 913 0 12,
  link 914 0 1 76 0 1,
  link 914 1 13 64 0 10,
  link 75 0 1 917 0 12,
  link 918 0 1 92 0 1,
  link 918 1 13 80 0 10,
  link 91 0 1 921 0 12,
  link 922 0 1 108 0 1,
  link 922 1 13 96 0 10,
  link 107 0 1 925 0 12,
  link 926 0 1 124 0 1,
  link 926 1 13 112 0 10,
  link 123 0 1 929 0 12,
  link 930 0 1 140 0 1,
  link 930 1 13 128 0 10,
  link 139 0 1 933 0 12,
  link 934 0 1 156 0 1,
  link 934 1 13 144 0 10,
  link 155 0 1 937 0 12,
  link 938 0 1 172 0 1,
  link 938 1 13 160 0 10,
  link 171 0 1 941 0 12,
  link 942 0 1 188 0 1,
  link 942 1 13 176 0 10,
  link 187 0 1 945 0 12,
  link 946 0 1 204 0 1,
  link 946 1 13 192 0 10,
  link 203 0 1 949 0 12,
  link 950 0 1 220 0 1,
  link 950 1 13 208 0 10,
  link 219 0 1 953 0 12,
  link 954 0 1 236 0 1,
  link 954 1 13 224 0 10,
  link 235 0 1 957 0 12,
  link 958 0 1 252 0 1,
  link 958 1 13 240 0 10,
  link 251 0 1 961 0 12,
  link 962 0 1 268 0 1,
  link 962 1 13 256 0 10,
  link 267 0 1 965 0 12,
  link 966 0 1 284 0 1,
  link 966 1 13 272 0 10,
  link 283 0 1 969 0 12,
  link 970 0 1 300 0 1,
  link 970 1 13 288 0 10,
  link 299 0 1 973 0 12,
  link 974 0 1 316 0 1,
  link 974 1 13 304 0 10,
  link 315 0 1 977 0 12,
  link 978 0 1 332 0 1,
  link 978 1 13 320 0 10,
  link 331 0 1 981 0 12,
  link 982 0 1 348 0 1,
  link 982 1 13 336 0 10,
  link 347 0 1 985 0 12,
  link 986 0 1 364 0 1,
  link 986 1 13 352 0 10,
  link 363 0 1 989 0 12,
  link 990 0 1 380 0 1,
  link 990 1 13 368 0 10,
  link 379 0 1 993 0 12,
  link 994 0 1 396 0 1,
  link 994 1 13 384 0 10,
  link 395 0 1 997 0 12,
  link 998 0 1 876 0 1,
  link 998 1 13 864 0 10,
  link 875 0 1 1001 0 12,
  link 1002 0 1 892 0 1,
  link 1002 1 13 880 0 10,
  link 891 0 1 1005 0 12,
  link 1006 0 1 908 0 1,
  link 1006 1 13 896 0 10]

structure Pattern where
  width : Nat
  start : Nat
  lastOffset : Nat
  deriving DecidableEq

/-- In each source pattern the nonzero kinds form a contiguous limb prefix;
columns are start+j. The sole nonzero offset is at the last active limb of
pattern10. This representation retains every one of the 224 source cells. -/
def sourcePatterns : Fin 14 → Pattern := ![
  ⟨16,0,0⟩,
  ⟨8,0,0⟩,
  ⟨6,2,0⟩,
  ⟨6,0,0⟩,
  ⟨2,0,0⟩,
  ⟨2,6,0⟩,
  ⟨1,0,0⟩,
  ⟨1,10,0⟩,
  ⟨1,1,0⟩,
  ⟨1,2,0⟩,
  ⟨8,8,1051521018⟩,
  ⟨8,2,0⟩,
  ⟨8,1,0⟩,
  ⟨8,8,0⟩]

/-- A small finite static certificate, independent of table/field/challenges.
Every one of the actual 272 endpoint occurrences lies inside the fixed mask. -/
theorem source_endpoints_active : ∀ index : Fin 136,
    rowActive (sourceLinks index).producer.row ∧
      rowActive (sourceLinks index).consumer.row := by
  decide

theorem source_pattern_ranges : ∀ pattern : Fin 14,
    (sourcePatterns pattern).start + (sourcePatterns pattern).width ≤ 16 := by
  decide

#print axioms source_endpoints_active
#print axioms source_pattern_ranges
end AspisV8.SelectedCopyLayout
