import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block19_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 241 i-2*unitVector 240 i)
      13 11 (-7) 244 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 120 244 (by decide),
      sourceChord_unit_even _ 120 244 (by decide)]
  decide
#print axioms block19_entry0_0

theorem block19_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 242 i-4*unitVector 240 i)
      13 11 (-7) 244 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 121 244 (by decide),
      sourceChord_unit_even _ 120 244 (by decide)]
  decide
#print axioms block19_entry0_1

theorem block19_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 241 i-2*unitVector 240 i)
      13 11 (-7) 243 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 120 243 (by decide),
      sourceChord_unit_even _ 120 243 (by decide)]
  decide
#print axioms block19_entry1_0

theorem block19_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 242 i-4*unitVector 240 i)
      13 11 (-7) 243 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 121 243 (by decide),
      sourceChord_unit_even _ 120 243 (by decide)]
  decide
#print axioms block19_entry1_1

theorem block20_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 243 i-8*unitVector 240 i)
      13 11 (-7) 245 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 121 245 (by decide),
      sourceChord_unit_even _ 120 245 (by decide)]
  decide
#print axioms block20_entry0_0

theorem block21_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 253 i-2*unitVector 252 i)
      13 11 (-7) 256 = 117440512 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 126 256 (by decide),
      sourceChord_unit_even _ 126 256 (by decide)]
  decide
#print axioms block21_entry0_0

theorem block22_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 255 i-8*unitVector 252 i)
      13 11 (-7) 258 = 117440512 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 127 258 (by decide),
      sourceChord_unit_even _ 126 258 (by decide)]
  decide
#print axioms block22_entry0_0

theorem block22_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 257 i-2*unitVector 256 i)
      13 11 (-7) 258 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 128 258 (by decide),
      sourceChord_unit_even _ 128 258 (by decide)]
  decide
#print axioms block22_entry0_1

theorem block22_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 255 i-8*unitVector 252 i)
      13 11 (-7) 257 = 184549376 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 127 257 (by decide),
      sourceChord_unit_even _ 126 257 (by decide)]
  decide
#print axioms block22_entry1_0

theorem block22_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 257 i-2*unitVector 256 i)
      13 11 (-7) 257 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 128 257 (by decide),
      sourceChord_unit_even _ 128 257 (by decide)]
  decide
#print axioms block22_entry1_1

theorem block23_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 267 i-8*unitVector 264 i)
      13 11 (-7) 269 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 133 269 (by decide),
      sourceChord_unit_even _ 132 269 (by decide)]
  decide
#print axioms block23_entry0_0

theorem block23_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 269 i-2*unitVector 268 i)
      13 11 (-7) 269 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 134 269 (by decide),
      sourceChord_unit_even _ 134 269 (by decide)]
  decide
#print axioms block23_entry0_1

theorem block23_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 270 i-4*unitVector 268 i)
      13 11 (-7) 269 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 135 269 (by decide),
      sourceChord_unit_even _ 134 269 (by decide)]
  decide
#print axioms block23_entry0_2

theorem block23_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 267 i-8*unitVector 264 i)
      13 11 (-7) 271 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 133 271 (by decide),
      sourceChord_unit_even _ 132 271 (by decide)]
  decide
#print axioms block23_entry1_0

theorem block23_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 269 i-2*unitVector 268 i)
      13 11 (-7) 271 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 134 271 (by decide),
      sourceChord_unit_even _ 134 271 (by decide)]
  decide
#print axioms block23_entry1_1

theorem block23_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 270 i-4*unitVector 268 i)
      13 11 (-7) 271 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 135 271 (by decide),
      sourceChord_unit_even _ 134 271 (by decide)]
  decide
#print axioms block23_entry1_2

theorem block23_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 267 i-8*unitVector 264 i)
      13 11 (-7) 270 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 133 270 (by decide),
      sourceChord_unit_even _ 132 270 (by decide)]
  decide
#print axioms block23_entry2_0

theorem block23_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 269 i-2*unitVector 268 i)
      13 11 (-7) 270 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 134 270 (by decide),
      sourceChord_unit_even _ 134 270 (by decide)]
  decide
#print axioms block23_entry2_1

theorem block23_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 270 i-4*unitVector 268 i)
      13 11 (-7) 270 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 135 270 (by decide),
      sourceChord_unit_even _ 134 270 (by decide)]
  decide
#print axioms block23_entry2_2

theorem block24_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 279 i-8*unitVector 276 i)
      13 11 (-7) 282 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 139 282 (by decide),
      sourceChord_unit_even _ 138 282 (by decide)]
  decide
#print axioms block24_entry0_0

theorem block25_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 281 i-2*unitVector 280 i)
      13 11 (-7) 284 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 140 284 (by decide),
      sourceChord_unit_even _ 140 284 (by decide)]
  decide
#print axioms block25_entry0_0

theorem block25_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 282 i-4*unitVector 280 i)
      13 11 (-7) 284 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 141 284 (by decide),
      sourceChord_unit_even _ 140 284 (by decide)]
  decide
#print axioms block25_entry0_1

theorem block25_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 281 i-2*unitVector 280 i)
      13 11 (-7) 283 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 140 283 (by decide),
      sourceChord_unit_even _ 140 283 (by decide)]
  decide
#print axioms block25_entry1_0

theorem block25_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 282 i-4*unitVector 280 i)
      13 11 (-7) 283 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 141 283 (by decide),
      sourceChord_unit_even _ 140 283 (by decide)]
  decide
#print axioms block25_entry1_1

theorem block26_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 293 i-2*unitVector 292 i)
      13 11 (-7) 296 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 146 296 (by decide),
      sourceChord_unit_even _ 146 296 (by decide)]
  decide
#print axioms block26_entry0_0

theorem block26_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 294 i-4*unitVector 292 i)
      13 11 (-7) 296 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 147 296 (by decide),
      sourceChord_unit_even _ 146 296 (by decide)]
  decide
#print axioms block26_entry0_1

theorem block26_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 293 i-2*unitVector 292 i)
      13 11 (-7) 295 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 146 295 (by decide),
      sourceChord_unit_even _ 146 295 (by decide)]
  decide
#print axioms block26_entry1_0

theorem block26_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 294 i-4*unitVector 292 i)
      13 11 (-7) 295 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 147 295 (by decide),
      sourceChord_unit_even _ 146 295 (by decide)]
  decide
#print axioms block26_entry1_1

theorem block27_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 295 i-8*unitVector 292 i)
      13 11 (-7) 297 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 147 297 (by decide),
      sourceChord_unit_even _ 146 297 (by decide)]
  decide
#print axioms block27_entry0_0

theorem block28_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 305 i-2*unitVector 304 i)
      13 11 (-7) 308 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 152 308 (by decide),
      sourceChord_unit_even _ 152 308 (by decide)]
  decide
#print axioms block28_entry0_0

theorem block29_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 307 i-8*unitVector 304 i)
      13 11 (-7) 310 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 153 310 (by decide),
      sourceChord_unit_even _ 152 310 (by decide)]
  decide
#print axioms block29_entry0_0

theorem block29_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 309 i-2*unitVector 308 i)
      13 11 (-7) 310 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 154 310 (by decide),
      sourceChord_unit_even _ 154 310 (by decide)]
  decide
#print axioms block29_entry0_1

end AspisV8R17.SourceBlocks
