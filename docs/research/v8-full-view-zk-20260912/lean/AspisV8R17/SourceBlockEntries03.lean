import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block29_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 307 i-8*unitVector 304 i)
      13 11 (-7) 309 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 153 309 (by decide),
      sourceChord_unit_even _ 152 309 (by decide)]
  decide
#print axioms block29_entry1_0

theorem block29_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 309 i-2*unitVector 308 i)
      13 11 (-7) 309 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 154 309 (by decide),
      sourceChord_unit_even _ 154 309 (by decide)]
  decide
#print axioms block29_entry1_1

theorem block30_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 319 i-8*unitVector 316 i)
      13 11 (-7) 321 = 738197504 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 159 321 (by decide),
      sourceChord_unit_even _ 158 321 (by decide)]
  decide
#print axioms block30_entry0_0

theorem block30_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 321 i-2*unitVector 320 i)
      13 11 (-7) 321 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 160 321 (by decide),
      sourceChord_unit_even _ 160 321 (by decide)]
  decide
#print axioms block30_entry0_1

theorem block30_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 322 i-4*unitVector 320 i)
      13 11 (-7) 321 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 161 321 (by decide),
      sourceChord_unit_even _ 160 321 (by decide)]
  decide
#print axioms block30_entry0_2

theorem block30_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 319 i-8*unitVector 316 i)
      13 11 (-7) 323 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 159 323 (by decide),
      sourceChord_unit_even _ 158 323 (by decide)]
  decide
#print axioms block30_entry1_0

theorem block30_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 321 i-2*unitVector 320 i)
      13 11 (-7) 323 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 160 323 (by decide),
      sourceChord_unit_even _ 160 323 (by decide)]
  decide
#print axioms block30_entry1_1

theorem block30_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 322 i-4*unitVector 320 i)
      13 11 (-7) 323 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 161 323 (by decide),
      sourceChord_unit_even _ 160 323 (by decide)]
  decide
#print axioms block30_entry1_2

theorem block30_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 319 i-8*unitVector 316 i)
      13 11 (-7) 322 = 469762048 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 159 322 (by decide),
      sourceChord_unit_even _ 158 322 (by decide)]
  decide
#print axioms block30_entry2_0

theorem block30_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 321 i-2*unitVector 320 i)
      13 11 (-7) 322 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 160 322 (by decide),
      sourceChord_unit_even _ 160 322 (by decide)]
  decide
#print axioms block30_entry2_1

theorem block30_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 322 i-4*unitVector 320 i)
      13 11 (-7) 322 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 161 322 (by decide),
      sourceChord_unit_even _ 160 322 (by decide)]
  decide
#print axioms block30_entry2_2

theorem block31_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 331 i-8*unitVector 328 i)
      13 11 (-7) 334 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 165 334 (by decide),
      sourceChord_unit_even _ 164 334 (by decide)]
  decide
#print axioms block31_entry0_0

theorem block32_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 333 i-2*unitVector 332 i)
      13 11 (-7) 336 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 166 336 (by decide),
      sourceChord_unit_even _ 166 336 (by decide)]
  decide
#print axioms block32_entry0_0

theorem block32_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 334 i-4*unitVector 332 i)
      13 11 (-7) 336 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 167 336 (by decide),
      sourceChord_unit_even _ 166 336 (by decide)]
  decide
#print axioms block32_entry0_1

theorem block32_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 333 i-2*unitVector 332 i)
      13 11 (-7) 335 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 166 335 (by decide),
      sourceChord_unit_even _ 166 335 (by decide)]
  decide
#print axioms block32_entry1_0

theorem block32_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 334 i-4*unitVector 332 i)
      13 11 (-7) 335 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 167 335 (by decide),
      sourceChord_unit_even _ 166 335 (by decide)]
  decide
#print axioms block32_entry1_1

theorem block33_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 345 i-2*unitVector 344 i)
      13 11 (-7) 348 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 172 348 (by decide),
      sourceChord_unit_even _ 172 348 (by decide)]
  decide
#print axioms block33_entry0_0

theorem block33_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 346 i-4*unitVector 344 i)
      13 11 (-7) 348 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 173 348 (by decide),
      sourceChord_unit_even _ 172 348 (by decide)]
  decide
#print axioms block33_entry0_1

theorem block33_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 345 i-2*unitVector 344 i)
      13 11 (-7) 347 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 172 347 (by decide),
      sourceChord_unit_even _ 172 347 (by decide)]
  decide
#print axioms block33_entry1_0

theorem block33_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 346 i-4*unitVector 344 i)
      13 11 (-7) 347 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 173 347 (by decide),
      sourceChord_unit_even _ 172 347 (by decide)]
  decide
#print axioms block33_entry1_1

theorem block34_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 347 i-8*unitVector 344 i)
      13 11 (-7) 349 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 173 349 (by decide),
      sourceChord_unit_even _ 172 349 (by decide)]
  decide
#print axioms block34_entry0_0

theorem block35_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 357 i-2*unitVector 356 i)
      13 11 (-7) 360 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 178 360 (by decide),
      sourceChord_unit_even _ 178 360 (by decide)]
  decide
#print axioms block35_entry0_0

theorem block36_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 359 i-8*unitVector 356 i)
      13 11 (-7) 362 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 179 362 (by decide),
      sourceChord_unit_even _ 178 362 (by decide)]
  decide
#print axioms block36_entry0_0

theorem block36_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 361 i-2*unitVector 360 i)
      13 11 (-7) 362 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 180 362 (by decide),
      sourceChord_unit_even _ 180 362 (by decide)]
  decide
#print axioms block36_entry0_1

theorem block36_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 359 i-8*unitVector 356 i)
      13 11 (-7) 361 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 179 361 (by decide),
      sourceChord_unit_even _ 178 361 (by decide)]
  decide
#print axioms block36_entry1_0

theorem block36_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 361 i-2*unitVector 360 i)
      13 11 (-7) 361 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 180 361 (by decide),
      sourceChord_unit_even _ 180 361 (by decide)]
  decide
#print axioms block36_entry1_1

theorem block37_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 371 i-8*unitVector 368 i)
      13 11 (-7) 373 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 185 373 (by decide),
      sourceChord_unit_even _ 184 373 (by decide)]
  decide
#print axioms block37_entry0_0

theorem block37_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 373 i-2*unitVector 372 i)
      13 11 (-7) 373 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 186 373 (by decide),
      sourceChord_unit_even _ 186 373 (by decide)]
  decide
#print axioms block37_entry0_1

theorem block37_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 374 i-4*unitVector 372 i)
      13 11 (-7) 373 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 187 373 (by decide),
      sourceChord_unit_even _ 186 373 (by decide)]
  decide
#print axioms block37_entry0_2

theorem block37_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 371 i-8*unitVector 368 i)
      13 11 (-7) 375 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 185 375 (by decide),
      sourceChord_unit_even _ 184 375 (by decide)]
  decide
#print axioms block37_entry1_0

theorem block37_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 373 i-2*unitVector 372 i)
      13 11 (-7) 375 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 186 375 (by decide),
      sourceChord_unit_even _ 186 375 (by decide)]
  decide
#print axioms block37_entry1_1

theorem block37_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 374 i-4*unitVector 372 i)
      13 11 (-7) 375 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 187 375 (by decide),
      sourceChord_unit_even _ 186 375 (by decide)]
  decide
#print axioms block37_entry1_2

end AspisV8R17.SourceBlocks
