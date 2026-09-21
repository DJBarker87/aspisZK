import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block105_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 917 i-2*unitVector 916 i)
      13 11 (-7) 918 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 458 918 (by decide),
      sourceChord_unit_even _ 458 918 (by decide)]
  decide
#print axioms block105_entry0_1

theorem block105_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 915 i-8*unitVector 912 i)
      13 11 (-7) 917 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 457 917 (by decide),
      sourceChord_unit_even _ 456 917 (by decide)]
  decide
#print axioms block105_entry1_0

theorem block105_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 917 i-2*unitVector 916 i)
      13 11 (-7) 917 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 458 917 (by decide),
      sourceChord_unit_even _ 458 917 (by decide)]
  decide
#print axioms block105_entry1_1

theorem block106_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 919 i-8*unitVector 916 i)
      13 11 (-7) 922 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 459 922 (by decide),
      sourceChord_unit_even _ 458 922 (by decide)]
  decide
#print axioms block106_entry0_0

theorem block106_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 921 i-2*unitVector 920 i)
      13 11 (-7) 922 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 460 922 (by decide),
      sourceChord_unit_even _ 460 922 (by decide)]
  decide
#print axioms block106_entry0_1

theorem block106_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 919 i-8*unitVector 916 i)
      13 11 (-7) 921 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 459 921 (by decide),
      sourceChord_unit_even _ 458 921 (by decide)]
  decide
#print axioms block106_entry1_0

theorem block106_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 921 i-2*unitVector 920 i)
      13 11 (-7) 921 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 460 921 (by decide),
      sourceChord_unit_even _ 460 921 (by decide)]
  decide
#print axioms block106_entry1_1

theorem block107_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 923 i-8*unitVector 920 i)
      13 11 (-7) 926 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 461 926 (by decide),
      sourceChord_unit_even _ 460 926 (by decide)]
  decide
#print axioms block107_entry0_0

theorem block107_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 925 i-2*unitVector 924 i)
      13 11 (-7) 926 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 462 926 (by decide),
      sourceChord_unit_even _ 462 926 (by decide)]
  decide
#print axioms block107_entry0_1

theorem block107_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 923 i-8*unitVector 920 i)
      13 11 (-7) 925 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 461 925 (by decide),
      sourceChord_unit_even _ 460 925 (by decide)]
  decide
#print axioms block107_entry1_0

theorem block107_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 925 i-2*unitVector 924 i)
      13 11 (-7) 925 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 462 925 (by decide),
      sourceChord_unit_even _ 462 925 (by decide)]
  decide
#print axioms block107_entry1_1

theorem block108_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 927 i-8*unitVector 924 i)
      13 11 (-7) 930 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 463 930 (by decide),
      sourceChord_unit_even _ 462 930 (by decide)]
  decide
#print axioms block108_entry0_0

theorem block108_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 929 i-2*unitVector 928 i)
      13 11 (-7) 930 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 464 930 (by decide),
      sourceChord_unit_even _ 464 930 (by decide)]
  decide
#print axioms block108_entry0_1

theorem block108_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 927 i-8*unitVector 924 i)
      13 11 (-7) 929 = 1476395008 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 463 929 (by decide),
      sourceChord_unit_even _ 462 929 (by decide)]
  decide
#print axioms block108_entry1_0

theorem block108_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 929 i-2*unitVector 928 i)
      13 11 (-7) 929 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 464 929 (by decide),
      sourceChord_unit_even _ 464 929 (by decide)]
  decide
#print axioms block108_entry1_1

theorem block109_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 931 i-8*unitVector 928 i)
      13 11 (-7) 934 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 465 934 (by decide),
      sourceChord_unit_even _ 464 934 (by decide)]
  decide
#print axioms block109_entry0_0

theorem block109_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 933 i-2*unitVector 932 i)
      13 11 (-7) 934 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 466 934 (by decide),
      sourceChord_unit_even _ 466 934 (by decide)]
  decide
#print axioms block109_entry0_1

theorem block109_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 931 i-8*unitVector 928 i)
      13 11 (-7) 933 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 465 933 (by decide),
      sourceChord_unit_even _ 464 933 (by decide)]
  decide
#print axioms block109_entry1_0

theorem block109_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 933 i-2*unitVector 932 i)
      13 11 (-7) 933 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 466 933 (by decide),
      sourceChord_unit_even _ 466 933 (by decide)]
  decide
#print axioms block109_entry1_1

theorem block110_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 935 i-8*unitVector 932 i)
      13 11 (-7) 938 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 467 938 (by decide),
      sourceChord_unit_even _ 466 938 (by decide)]
  decide
#print axioms block110_entry0_0

theorem block110_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 937 i-2*unitVector 936 i)
      13 11 (-7) 938 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 468 938 (by decide),
      sourceChord_unit_even _ 468 938 (by decide)]
  decide
#print axioms block110_entry0_1

theorem block110_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 935 i-8*unitVector 932 i)
      13 11 (-7) 937 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 467 937 (by decide),
      sourceChord_unit_even _ 466 937 (by decide)]
  decide
#print axioms block110_entry1_0

theorem block110_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 937 i-2*unitVector 936 i)
      13 11 (-7) 937 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 468 937 (by decide),
      sourceChord_unit_even _ 468 937 (by decide)]
  decide
#print axioms block110_entry1_1

theorem block111_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 939 i-8*unitVector 936 i)
      13 11 (-7) 942 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 469 942 (by decide),
      sourceChord_unit_even _ 468 942 (by decide)]
  decide
#print axioms block111_entry0_0

theorem block111_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 941 i-2*unitVector 940 i)
      13 11 (-7) 942 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 470 942 (by decide),
      sourceChord_unit_even _ 470 942 (by decide)]
  decide
#print axioms block111_entry0_1

theorem block111_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 939 i-8*unitVector 936 i)
      13 11 (-7) 941 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 469 941 (by decide),
      sourceChord_unit_even _ 468 941 (by decide)]
  decide
#print axioms block111_entry1_0

theorem block111_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 941 i-2*unitVector 940 i)
      13 11 (-7) 941 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 470 941 (by decide),
      sourceChord_unit_even _ 470 941 (by decide)]
  decide
#print axioms block111_entry1_1

theorem block112_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 943 i-8*unitVector 940 i)
      13 11 (-7) 946 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 471 946 (by decide),
      sourceChord_unit_even _ 470 946 (by decide)]
  decide
#print axioms block112_entry0_0

theorem block112_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 945 i-2*unitVector 944 i)
      13 11 (-7) 946 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 472 946 (by decide),
      sourceChord_unit_even _ 472 946 (by decide)]
  decide
#print axioms block112_entry0_1

theorem block112_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 943 i-8*unitVector 940 i)
      13 11 (-7) 945 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 471 945 (by decide),
      sourceChord_unit_even _ 470 945 (by decide)]
  decide
#print axioms block112_entry1_0

theorem block112_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 945 i-2*unitVector 944 i)
      13 11 (-7) 945 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 472 945 (by decide),
      sourceChord_unit_even _ 472 945 (by decide)]
  decide
#print axioms block112_entry1_1

theorem block113_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 947 i-8*unitVector 944 i)
      13 11 (-7) 950 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 473 950 (by decide),
      sourceChord_unit_even _ 472 950 (by decide)]
  decide
#print axioms block113_entry0_0

end AspisV8R17.SourceBlocks
