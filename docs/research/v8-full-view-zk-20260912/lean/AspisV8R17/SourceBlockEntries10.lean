import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block113_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 949 i-2*unitVector 948 i)
      13 11 (-7) 950 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 474 950 (by decide),
      sourceChord_unit_even _ 474 950 (by decide)]
  decide
#print axioms block113_entry0_1

theorem block113_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 947 i-8*unitVector 944 i)
      13 11 (-7) 949 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 473 949 (by decide),
      sourceChord_unit_even _ 472 949 (by decide)]
  decide
#print axioms block113_entry1_0

theorem block113_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 949 i-2*unitVector 948 i)
      13 11 (-7) 949 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 474 949 (by decide),
      sourceChord_unit_even _ 474 949 (by decide)]
  decide
#print axioms block113_entry1_1

theorem block114_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 951 i-8*unitVector 948 i)
      13 11 (-7) 954 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 475 954 (by decide),
      sourceChord_unit_even _ 474 954 (by decide)]
  decide
#print axioms block114_entry0_0

theorem block114_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 953 i-2*unitVector 952 i)
      13 11 (-7) 954 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 476 954 (by decide),
      sourceChord_unit_even _ 476 954 (by decide)]
  decide
#print axioms block114_entry0_1

theorem block114_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 951 i-8*unitVector 948 i)
      13 11 (-7) 953 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 475 953 (by decide),
      sourceChord_unit_even _ 474 953 (by decide)]
  decide
#print axioms block114_entry1_0

theorem block114_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 953 i-2*unitVector 952 i)
      13 11 (-7) 953 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 476 953 (by decide),
      sourceChord_unit_even _ 476 953 (by decide)]
  decide
#print axioms block114_entry1_1

theorem block115_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 955 i-8*unitVector 952 i)
      13 11 (-7) 958 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 477 958 (by decide),
      sourceChord_unit_even _ 476 958 (by decide)]
  decide
#print axioms block115_entry0_0

theorem block115_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 957 i-2*unitVector 956 i)
      13 11 (-7) 958 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 478 958 (by decide),
      sourceChord_unit_even _ 478 958 (by decide)]
  decide
#print axioms block115_entry0_1

theorem block115_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 955 i-8*unitVector 952 i)
      13 11 (-7) 957 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 477 957 (by decide),
      sourceChord_unit_even _ 476 957 (by decide)]
  decide
#print axioms block115_entry1_0

theorem block115_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 957 i-2*unitVector 956 i)
      13 11 (-7) 957 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 478 957 (by decide),
      sourceChord_unit_even _ 478 957 (by decide)]
  decide
#print axioms block115_entry1_1

theorem block116_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 959 i-8*unitVector 956 i)
      13 11 (-7) 962 = 469762048 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 479 962 (by decide),
      sourceChord_unit_even _ 478 962 (by decide)]
  decide
#print axioms block116_entry0_0

theorem block116_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 961 i-2*unitVector 960 i)
      13 11 (-7) 962 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 480 962 (by decide),
      sourceChord_unit_even _ 480 962 (by decide)]
  decide
#print axioms block116_entry0_1

theorem block116_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 959 i-8*unitVector 956 i)
      13 11 (-7) 961 = 738197504 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 479 961 (by decide),
      sourceChord_unit_even _ 478 961 (by decide)]
  decide
#print axioms block116_entry1_0

theorem block116_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 961 i-2*unitVector 960 i)
      13 11 (-7) 961 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 480 961 (by decide),
      sourceChord_unit_even _ 480 961 (by decide)]
  decide
#print axioms block116_entry1_1

theorem block117_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 963 i-8*unitVector 960 i)
      13 11 (-7) 966 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 481 966 (by decide),
      sourceChord_unit_even _ 480 966 (by decide)]
  decide
#print axioms block117_entry0_0

theorem block117_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 965 i-2*unitVector 964 i)
      13 11 (-7) 966 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 482 966 (by decide),
      sourceChord_unit_even _ 482 966 (by decide)]
  decide
#print axioms block117_entry0_1

theorem block117_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 963 i-8*unitVector 960 i)
      13 11 (-7) 965 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 481 965 (by decide),
      sourceChord_unit_even _ 480 965 (by decide)]
  decide
#print axioms block117_entry1_0

theorem block117_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 965 i-2*unitVector 964 i)
      13 11 (-7) 965 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 482 965 (by decide),
      sourceChord_unit_even _ 482 965 (by decide)]
  decide
#print axioms block117_entry1_1

theorem block118_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 967 i-8*unitVector 964 i)
      13 11 (-7) 970 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 483 970 (by decide),
      sourceChord_unit_even _ 482 970 (by decide)]
  decide
#print axioms block118_entry0_0

theorem block118_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 969 i-2*unitVector 968 i)
      13 11 (-7) 970 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 484 970 (by decide),
      sourceChord_unit_even _ 484 970 (by decide)]
  decide
#print axioms block118_entry0_1

theorem block118_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 967 i-8*unitVector 964 i)
      13 11 (-7) 969 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 483 969 (by decide),
      sourceChord_unit_even _ 482 969 (by decide)]
  decide
#print axioms block118_entry1_0

theorem block118_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 969 i-2*unitVector 968 i)
      13 11 (-7) 969 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 484 969 (by decide),
      sourceChord_unit_even _ 484 969 (by decide)]
  decide
#print axioms block118_entry1_1

theorem block119_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 971 i-8*unitVector 968 i)
      13 11 (-7) 974 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 485 974 (by decide),
      sourceChord_unit_even _ 484 974 (by decide)]
  decide
#print axioms block119_entry0_0

theorem block119_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 973 i-2*unitVector 972 i)
      13 11 (-7) 974 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 486 974 (by decide),
      sourceChord_unit_even _ 486 974 (by decide)]
  decide
#print axioms block119_entry0_1

theorem block119_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 971 i-8*unitVector 968 i)
      13 11 (-7) 973 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 485 973 (by decide),
      sourceChord_unit_even _ 484 973 (by decide)]
  decide
#print axioms block119_entry1_0

theorem block119_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 973 i-2*unitVector 972 i)
      13 11 (-7) 973 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 486 973 (by decide),
      sourceChord_unit_even _ 486 973 (by decide)]
  decide
#print axioms block119_entry1_1

theorem block120_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 975 i-8*unitVector 972 i)
      13 11 (-7) 978 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 487 978 (by decide),
      sourceChord_unit_even _ 486 978 (by decide)]
  decide
#print axioms block120_entry0_0

theorem block120_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 977 i-2*unitVector 976 i)
      13 11 (-7) 978 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 488 978 (by decide),
      sourceChord_unit_even _ 488 978 (by decide)]
  decide
#print axioms block120_entry0_1

theorem block120_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 975 i-8*unitVector 972 i)
      13 11 (-7) 977 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 487 977 (by decide),
      sourceChord_unit_even _ 486 977 (by decide)]
  decide
#print axioms block120_entry1_0

theorem block120_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 977 i-2*unitVector 976 i)
      13 11 (-7) 977 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 488 977 (by decide),
      sourceChord_unit_even _ 488 977 (by decide)]
  decide
#print axioms block120_entry1_1

theorem block121_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 979 i-8*unitVector 976 i)
      13 11 (-7) 982 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 489 982 (by decide),
      sourceChord_unit_even _ 488 982 (by decide)]
  decide
#print axioms block121_entry0_0

end AspisV8R17.SourceBlocks
