import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block0_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 97 i-2*unitVector 96 i)
      13 11 (-7) 100 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 48 100 (by decide),
      sourceChord_unit_even _ 48 100 (by decide)]
  decide
#print axioms block0_entry0_0

theorem block1_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 99 i-8*unitVector 96 i)
      13 11 (-7) 101 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 49 101 (by decide),
      sourceChord_unit_even _ 48 101 (by decide)]
  decide
#print axioms block1_entry0_0

theorem block2_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 111 i-8*unitVector 108 i)
      13 11 (-7) 113 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 55 113 (by decide),
      sourceChord_unit_even _ 54 113 (by decide)]
  decide
#print axioms block2_entry0_0

theorem block2_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 113 i-2*unitVector 112 i)
      13 11 (-7) 113 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 56 113 (by decide),
      sourceChord_unit_even _ 56 113 (by decide)]
  decide
#print axioms block2_entry0_1

theorem block2_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 114 i-4*unitVector 112 i)
      13 11 (-7) 113 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 57 113 (by decide),
      sourceChord_unit_even _ 56 113 (by decide)]
  decide
#print axioms block2_entry0_2

theorem block2_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 111 i-8*unitVector 108 i)
      13 11 (-7) 115 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 55 115 (by decide),
      sourceChord_unit_even _ 54 115 (by decide)]
  decide
#print axioms block2_entry1_0

theorem block2_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 113 i-2*unitVector 112 i)
      13 11 (-7) 115 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 56 115 (by decide),
      sourceChord_unit_even _ 56 115 (by decide)]
  decide
#print axioms block2_entry1_1

theorem block2_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 114 i-4*unitVector 112 i)
      13 11 (-7) 115 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 57 115 (by decide),
      sourceChord_unit_even _ 56 115 (by decide)]
  decide
#print axioms block2_entry1_2

theorem block2_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 111 i-8*unitVector 108 i)
      13 11 (-7) 114 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 55 114 (by decide),
      sourceChord_unit_even _ 54 114 (by decide)]
  decide
#print axioms block2_entry2_0

theorem block2_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 113 i-2*unitVector 112 i)
      13 11 (-7) 114 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 56 114 (by decide),
      sourceChord_unit_even _ 56 114 (by decide)]
  decide
#print axioms block2_entry2_1

theorem block2_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 114 i-4*unitVector 112 i)
      13 11 (-7) 114 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 57 114 (by decide),
      sourceChord_unit_even _ 56 114 (by decide)]
  decide
#print axioms block2_entry2_2

theorem block3_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 123 i-8*unitVector 120 i)
      13 11 (-7) 126 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 61 126 (by decide),
      sourceChord_unit_even _ 60 126 (by decide)]
  decide
#print axioms block3_entry0_0

theorem block4_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 125 i-2*unitVector 124 i)
      13 11 (-7) 128 = 234881024 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 62 128 (by decide),
      sourceChord_unit_even _ 62 128 (by decide)]
  decide
#print axioms block4_entry0_0

theorem block4_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 126 i-4*unitVector 124 i)
      13 11 (-7) 128 = 369098752 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 63 128 (by decide),
      sourceChord_unit_even _ 62 128 (by decide)]
  decide
#print axioms block4_entry0_1

theorem block4_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 125 i-2*unitVector 124 i)
      13 11 (-7) 127 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 62 127 (by decide),
      sourceChord_unit_even _ 62 127 (by decide)]
  decide
#print axioms block4_entry1_0

theorem block4_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 126 i-4*unitVector 124 i)
      13 11 (-7) 127 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 63 127 (by decide),
      sourceChord_unit_even _ 62 127 (by decide)]
  decide
#print axioms block4_entry1_1

theorem block5_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 137 i-2*unitVector 136 i)
      13 11 (-7) 140 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 68 140 (by decide),
      sourceChord_unit_even _ 68 140 (by decide)]
  decide
#print axioms block5_entry0_0

theorem block5_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 138 i-4*unitVector 136 i)
      13 11 (-7) 140 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 69 140 (by decide),
      sourceChord_unit_even _ 68 140 (by decide)]
  decide
#print axioms block5_entry0_1

theorem block5_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 137 i-2*unitVector 136 i)
      13 11 (-7) 139 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 68 139 (by decide),
      sourceChord_unit_even _ 68 139 (by decide)]
  decide
#print axioms block5_entry1_0

theorem block5_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 138 i-4*unitVector 136 i)
      13 11 (-7) 139 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 69 139 (by decide),
      sourceChord_unit_even _ 68 139 (by decide)]
  decide
#print axioms block5_entry1_1

theorem block6_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 139 i-8*unitVector 136 i)
      13 11 (-7) 141 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 69 141 (by decide),
      sourceChord_unit_even _ 68 141 (by decide)]
  decide
#print axioms block6_entry0_0

theorem block7_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 149 i-2*unitVector 148 i)
      13 11 (-7) 152 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 74 152 (by decide),
      sourceChord_unit_even _ 74 152 (by decide)]
  decide
#print axioms block7_entry0_0

theorem block8_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 151 i-8*unitVector 148 i)
      13 11 (-7) 154 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 75 154 (by decide),
      sourceChord_unit_even _ 74 154 (by decide)]
  decide
#print axioms block8_entry0_0

theorem block8_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 153 i-2*unitVector 152 i)
      13 11 (-7) 154 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 76 154 (by decide),
      sourceChord_unit_even _ 76 154 (by decide)]
  decide
#print axioms block8_entry0_1

theorem block8_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 151 i-8*unitVector 148 i)
      13 11 (-7) 153 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 75 153 (by decide),
      sourceChord_unit_even _ 74 153 (by decide)]
  decide
#print axioms block8_entry1_0

theorem block8_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 153 i-2*unitVector 152 i)
      13 11 (-7) 153 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 76 153 (by decide),
      sourceChord_unit_even _ 76 153 (by decide)]
  decide
#print axioms block8_entry1_1

theorem block9_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 163 i-8*unitVector 160 i)
      13 11 (-7) 165 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 81 165 (by decide),
      sourceChord_unit_even _ 80 165 (by decide)]
  decide
#print axioms block9_entry0_0

theorem block9_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 165 i-2*unitVector 164 i)
      13 11 (-7) 165 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 82 165 (by decide),
      sourceChord_unit_even _ 82 165 (by decide)]
  decide
#print axioms block9_entry0_1

theorem block9_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 166 i-4*unitVector 164 i)
      13 11 (-7) 165 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 83 165 (by decide),
      sourceChord_unit_even _ 82 165 (by decide)]
  decide
#print axioms block9_entry0_2

theorem block9_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 163 i-8*unitVector 160 i)
      13 11 (-7) 167 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 81 167 (by decide),
      sourceChord_unit_even _ 80 167 (by decide)]
  decide
#print axioms block9_entry1_0

theorem block9_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 165 i-2*unitVector 164 i)
      13 11 (-7) 167 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 82 167 (by decide),
      sourceChord_unit_even _ 82 167 (by decide)]
  decide
#print axioms block9_entry1_1

theorem block9_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 166 i-4*unitVector 164 i)
      13 11 (-7) 167 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 83 167 (by decide),
      sourceChord_unit_even _ 82 167 (by decide)]
  decide
#print axioms block9_entry1_2

end AspisV8R17.SourceBlocks
