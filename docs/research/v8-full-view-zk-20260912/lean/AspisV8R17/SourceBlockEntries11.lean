import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block121_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 981 i-2*unitVector 980 i)
      13 11 (-7) 982 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 490 982 (by decide),
      sourceChord_unit_even _ 490 982 (by decide)]
  decide
#print axioms block121_entry0_1

theorem block121_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 979 i-8*unitVector 976 i)
      13 11 (-7) 981 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 489 981 (by decide),
      sourceChord_unit_even _ 488 981 (by decide)]
  decide
#print axioms block121_entry1_0

theorem block121_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 981 i-2*unitVector 980 i)
      13 11 (-7) 981 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 490 981 (by decide),
      sourceChord_unit_even _ 490 981 (by decide)]
  decide
#print axioms block121_entry1_1

theorem block122_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 983 i-8*unitVector 980 i)
      13 11 (-7) 986 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 491 986 (by decide),
      sourceChord_unit_even _ 490 986 (by decide)]
  decide
#print axioms block122_entry0_0

theorem block122_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 985 i-2*unitVector 984 i)
      13 11 (-7) 986 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 492 986 (by decide),
      sourceChord_unit_even _ 492 986 (by decide)]
  decide
#print axioms block122_entry0_1

theorem block122_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 983 i-8*unitVector 980 i)
      13 11 (-7) 985 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 491 985 (by decide),
      sourceChord_unit_even _ 490 985 (by decide)]
  decide
#print axioms block122_entry1_0

theorem block122_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 985 i-2*unitVector 984 i)
      13 11 (-7) 985 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 492 985 (by decide),
      sourceChord_unit_even _ 492 985 (by decide)]
  decide
#print axioms block122_entry1_1

theorem block123_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 987 i-8*unitVector 984 i)
      13 11 (-7) 990 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 493 990 (by decide),
      sourceChord_unit_even _ 492 990 (by decide)]
  decide
#print axioms block123_entry0_0

theorem block123_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 989 i-2*unitVector 988 i)
      13 11 (-7) 990 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 494 990 (by decide),
      sourceChord_unit_even _ 494 990 (by decide)]
  decide
#print axioms block123_entry0_1

theorem block123_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 987 i-8*unitVector 984 i)
      13 11 (-7) 989 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 493 989 (by decide),
      sourceChord_unit_even _ 492 989 (by decide)]
  decide
#print axioms block123_entry1_0

theorem block123_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 989 i-2*unitVector 988 i)
      13 11 (-7) 989 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 494 989 (by decide),
      sourceChord_unit_even _ 494 989 (by decide)]
  decide
#print axioms block123_entry1_1

theorem block124_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 991 i-8*unitVector 988 i)
      13 11 (-7) 994 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 495 994 (by decide),
      sourceChord_unit_even _ 494 994 (by decide)]
  decide
#print axioms block124_entry0_0

theorem block124_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 993 i-2*unitVector 992 i)
      13 11 (-7) 994 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 496 994 (by decide),
      sourceChord_unit_even _ 496 994 (by decide)]
  decide
#print axioms block124_entry0_1

theorem block124_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 991 i-8*unitVector 988 i)
      13 11 (-7) 993 = 1476395008 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 495 993 (by decide),
      sourceChord_unit_even _ 494 993 (by decide)]
  decide
#print axioms block124_entry1_0

theorem block124_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 993 i-2*unitVector 992 i)
      13 11 (-7) 993 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 496 993 (by decide),
      sourceChord_unit_even _ 496 993 (by decide)]
  decide
#print axioms block124_entry1_1

theorem block125_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 995 i-8*unitVector 992 i)
      13 11 (-7) 998 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 497 998 (by decide),
      sourceChord_unit_even _ 496 998 (by decide)]
  decide
#print axioms block125_entry0_0

theorem block125_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 997 i-2*unitVector 996 i)
      13 11 (-7) 998 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 498 998 (by decide),
      sourceChord_unit_even _ 498 998 (by decide)]
  decide
#print axioms block125_entry0_1

theorem block125_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 995 i-8*unitVector 992 i)
      13 11 (-7) 997 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 497 997 (by decide),
      sourceChord_unit_even _ 496 997 (by decide)]
  decide
#print axioms block125_entry1_0

theorem block125_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 997 i-2*unitVector 996 i)
      13 11 (-7) 997 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 498 997 (by decide),
      sourceChord_unit_even _ 498 997 (by decide)]
  decide
#print axioms block125_entry1_1

theorem block126_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 999 i-8*unitVector 996 i)
      13 11 (-7) 1002 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 499 1002 (by decide),
      sourceChord_unit_even _ 498 1002 (by decide)]
  decide
#print axioms block126_entry0_0

theorem block126_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1001 i-2*unitVector 1000 i)
      13 11 (-7) 1002 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 500 1002 (by decide),
      sourceChord_unit_even _ 500 1002 (by decide)]
  decide
#print axioms block126_entry0_1

theorem block126_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 999 i-8*unitVector 996 i)
      13 11 (-7) 1001 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 499 1001 (by decide),
      sourceChord_unit_even _ 498 1001 (by decide)]
  decide
#print axioms block126_entry1_0

theorem block126_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1001 i-2*unitVector 1000 i)
      13 11 (-7) 1001 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 500 1001 (by decide),
      sourceChord_unit_even _ 500 1001 (by decide)]
  decide
#print axioms block126_entry1_1

theorem block127_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1003 i-8*unitVector 1000 i)
      13 11 (-7) 1005 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 501 1005 (by decide),
      sourceChord_unit_even _ 500 1005 (by decide)]
  decide
#print axioms block127_entry0_0

theorem block127_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1005 i-2*unitVector 1004 i)
      13 11 (-7) 1005 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 502 1005 (by decide),
      sourceChord_unit_even _ 502 1005 (by decide)]
  decide
#print axioms block127_entry0_1

theorem block127_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1006 i-4*unitVector 1004 i)
      13 11 (-7) 1005 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 503 1005 (by decide),
      sourceChord_unit_even _ 502 1005 (by decide)]
  decide
#print axioms block127_entry0_2

theorem block127_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1003 i-8*unitVector 1000 i)
      13 11 (-7) 1008 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 501 1008 (by decide),
      sourceChord_unit_even _ 500 1008 (by decide)]
  decide
#print axioms block127_entry1_0

theorem block127_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1005 i-2*unitVector 1004 i)
      13 11 (-7) 1008 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 502 1008 (by decide),
      sourceChord_unit_even _ 502 1008 (by decide)]
  decide
#print axioms block127_entry1_1

theorem block127_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1006 i-4*unitVector 1004 i)
      13 11 (-7) 1008 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 503 1008 (by decide),
      sourceChord_unit_even _ 502 1008 (by decide)]
  decide
#print axioms block127_entry1_2

theorem block127_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1003 i-8*unitVector 1000 i)
      13 11 (-7) 1006 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 501 1006 (by decide),
      sourceChord_unit_even _ 500 1006 (by decide)]
  decide
#print axioms block127_entry2_0

theorem block127_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1005 i-2*unitVector 1004 i)
      13 11 (-7) 1006 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 502 1006 (by decide),
      sourceChord_unit_even _ 502 1006 (by decide)]
  decide
#print axioms block127_entry2_1

theorem block127_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1006 i-4*unitVector 1004 i)
      13 11 (-7) 1006 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 503 1006 (by decide),
      sourceChord_unit_even _ 502 1006 (by decide)]
  decide
#print axioms block127_entry2_2

end AspisV8R17.SourceBlocks
