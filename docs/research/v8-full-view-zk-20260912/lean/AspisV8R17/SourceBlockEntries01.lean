import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block9_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 163 i-8*unitVector 160 i)
      13 11 (-7) 166 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 81 166 (by decide),
      sourceChord_unit_even _ 80 166 (by decide)]
  decide
#print axioms block9_entry2_0

theorem block9_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 165 i-2*unitVector 164 i)
      13 11 (-7) 166 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 82 166 (by decide),
      sourceChord_unit_even _ 82 166 (by decide)]
  decide
#print axioms block9_entry2_1

theorem block9_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 166 i-4*unitVector 164 i)
      13 11 (-7) 166 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 83 166 (by decide),
      sourceChord_unit_even _ 82 166 (by decide)]
  decide
#print axioms block9_entry2_2

theorem block10_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 175 i-8*unitVector 172 i)
      13 11 (-7) 178 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 87 178 (by decide),
      sourceChord_unit_even _ 86 178 (by decide)]
  decide
#print axioms block10_entry0_0

theorem block11_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 177 i-2*unitVector 176 i)
      13 11 (-7) 180 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 88 180 (by decide),
      sourceChord_unit_even _ 88 180 (by decide)]
  decide
#print axioms block11_entry0_0

theorem block11_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 178 i-4*unitVector 176 i)
      13 11 (-7) 180 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 89 180 (by decide),
      sourceChord_unit_even _ 88 180 (by decide)]
  decide
#print axioms block11_entry0_1

theorem block11_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 177 i-2*unitVector 176 i)
      13 11 (-7) 179 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 88 179 (by decide),
      sourceChord_unit_even _ 88 179 (by decide)]
  decide
#print axioms block11_entry1_0

theorem block11_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 178 i-4*unitVector 176 i)
      13 11 (-7) 179 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 89 179 (by decide),
      sourceChord_unit_even _ 88 179 (by decide)]
  decide
#print axioms block11_entry1_1

theorem block12_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 189 i-2*unitVector 188 i)
      13 11 (-7) 192 = 469762048 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 94 192 (by decide),
      sourceChord_unit_even _ 94 192 (by decide)]
  decide
#print axioms block12_entry0_0

theorem block12_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 190 i-4*unitVector 188 i)
      13 11 (-7) 192 = 738197504 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 95 192 (by decide),
      sourceChord_unit_even _ 94 192 (by decide)]
  decide
#print axioms block12_entry0_1

theorem block12_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 189 i-2*unitVector 188 i)
      13 11 (-7) 191 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 94 191 (by decide),
      sourceChord_unit_even _ 94 191 (by decide)]
  decide
#print axioms block12_entry1_0

theorem block12_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 190 i-4*unitVector 188 i)
      13 11 (-7) 191 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 95 191 (by decide),
      sourceChord_unit_even _ 94 191 (by decide)]
  decide
#print axioms block12_entry1_1

theorem block13_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 191 i-8*unitVector 188 i)
      13 11 (-7) 193 = 738197504 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 95 193 (by decide),
      sourceChord_unit_even _ 94 193 (by decide)]
  decide
#print axioms block13_entry0_0

theorem block14_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 201 i-2*unitVector 200 i)
      13 11 (-7) 204 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 100 204 (by decide),
      sourceChord_unit_even _ 100 204 (by decide)]
  decide
#print axioms block14_entry0_0

theorem block15_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 203 i-8*unitVector 200 i)
      13 11 (-7) 206 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 101 206 (by decide),
      sourceChord_unit_even _ 100 206 (by decide)]
  decide
#print axioms block15_entry0_0

theorem block15_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 205 i-2*unitVector 204 i)
      13 11 (-7) 206 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 102 206 (by decide),
      sourceChord_unit_even _ 102 206 (by decide)]
  decide
#print axioms block15_entry0_1

theorem block15_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 203 i-8*unitVector 200 i)
      13 11 (-7) 205 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 101 205 (by decide),
      sourceChord_unit_even _ 100 205 (by decide)]
  decide
#print axioms block15_entry1_0

theorem block15_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 205 i-2*unitVector 204 i)
      13 11 (-7) 205 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 102 205 (by decide),
      sourceChord_unit_even _ 102 205 (by decide)]
  decide
#print axioms block15_entry1_1

theorem block16_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 215 i-8*unitVector 212 i)
      13 11 (-7) 217 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 107 217 (by decide),
      sourceChord_unit_even _ 106 217 (by decide)]
  decide
#print axioms block16_entry0_0

theorem block16_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 217 i-2*unitVector 216 i)
      13 11 (-7) 217 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 108 217 (by decide),
      sourceChord_unit_even _ 108 217 (by decide)]
  decide
#print axioms block16_entry0_1

theorem block16_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 218 i-4*unitVector 216 i)
      13 11 (-7) 217 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 109 217 (by decide),
      sourceChord_unit_even _ 108 217 (by decide)]
  decide
#print axioms block16_entry0_2

theorem block16_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 215 i-8*unitVector 212 i)
      13 11 (-7) 219 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 107 219 (by decide),
      sourceChord_unit_even _ 106 219 (by decide)]
  decide
#print axioms block16_entry1_0

theorem block16_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 217 i-2*unitVector 216 i)
      13 11 (-7) 219 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 108 219 (by decide),
      sourceChord_unit_even _ 108 219 (by decide)]
  decide
#print axioms block16_entry1_1

theorem block16_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 218 i-4*unitVector 216 i)
      13 11 (-7) 219 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 109 219 (by decide),
      sourceChord_unit_even _ 108 219 (by decide)]
  decide
#print axioms block16_entry1_2

theorem block16_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 215 i-8*unitVector 212 i)
      13 11 (-7) 218 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 107 218 (by decide),
      sourceChord_unit_even _ 106 218 (by decide)]
  decide
#print axioms block16_entry2_0

theorem block16_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 217 i-2*unitVector 216 i)
      13 11 (-7) 218 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 108 218 (by decide),
      sourceChord_unit_even _ 108 218 (by decide)]
  decide
#print axioms block16_entry2_1

theorem block16_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 218 i-4*unitVector 216 i)
      13 11 (-7) 218 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 109 218 (by decide),
      sourceChord_unit_even _ 108 218 (by decide)]
  decide
#print axioms block16_entry2_2

theorem block17_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 227 i-8*unitVector 224 i)
      13 11 (-7) 230 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 113 230 (by decide),
      sourceChord_unit_even _ 112 230 (by decide)]
  decide
#print axioms block17_entry0_0

theorem block18_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 229 i-2*unitVector 228 i)
      13 11 (-7) 232 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 114 232 (by decide),
      sourceChord_unit_even _ 114 232 (by decide)]
  decide
#print axioms block18_entry0_0

theorem block18_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 230 i-4*unitVector 228 i)
      13 11 (-7) 232 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 115 232 (by decide),
      sourceChord_unit_even _ 114 232 (by decide)]
  decide
#print axioms block18_entry0_1

theorem block18_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 229 i-2*unitVector 228 i)
      13 11 (-7) 231 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 114 231 (by decide),
      sourceChord_unit_even _ 114 231 (by decide)]
  decide
#print axioms block18_entry1_0

theorem block18_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 230 i-4*unitVector 228 i)
      13 11 (-7) 231 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 115 231 (by decide),
      sourceChord_unit_even _ 114 231 (by decide)]
  decide
#print axioms block18_entry1_1

end AspisV8R17.SourceBlocks
