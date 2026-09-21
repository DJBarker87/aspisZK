import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block37_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 371 i-8*unitVector 368 i)
      13 11 (-7) 374 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 185 374 (by decide),
      sourceChord_unit_even _ 184 374 (by decide)]
  decide
#print axioms block37_entry2_0

theorem block37_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 373 i-2*unitVector 372 i)
      13 11 (-7) 374 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 186 374 (by decide),
      sourceChord_unit_even _ 186 374 (by decide)]
  decide
#print axioms block37_entry2_1

theorem block37_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 374 i-4*unitVector 372 i)
      13 11 (-7) 374 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 187 374 (by decide),
      sourceChord_unit_even _ 186 374 (by decide)]
  decide
#print axioms block37_entry2_2

theorem block38_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 383 i-8*unitVector 380 i)
      13 11 (-7) 386 = 234881024 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 191 386 (by decide),
      sourceChord_unit_even _ 190 386 (by decide)]
  decide
#print axioms block38_entry0_0

theorem block39_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 385 i-2*unitVector 384 i)
      13 11 (-7) 388 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 192 388 (by decide),
      sourceChord_unit_even _ 192 388 (by decide)]
  decide
#print axioms block39_entry0_0

theorem block39_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 386 i-4*unitVector 384 i)
      13 11 (-7) 388 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 193 388 (by decide),
      sourceChord_unit_even _ 192 388 (by decide)]
  decide
#print axioms block39_entry0_1

theorem block39_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 385 i-2*unitVector 384 i)
      13 11 (-7) 387 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 192 387 (by decide),
      sourceChord_unit_even _ 192 387 (by decide)]
  decide
#print axioms block39_entry1_0

theorem block39_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 386 i-4*unitVector 384 i)
      13 11 (-7) 387 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 193 387 (by decide),
      sourceChord_unit_even _ 192 387 (by decide)]
  decide
#print axioms block39_entry1_1

theorem block40_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 397 i-2*unitVector 396 i)
      13 11 (-7) 400 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 198 400 (by decide),
      sourceChord_unit_even _ 198 400 (by decide)]
  decide
#print axioms block40_entry0_0

theorem block40_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 398 i-4*unitVector 396 i)
      13 11 (-7) 400 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 199 400 (by decide),
      sourceChord_unit_even _ 198 400 (by decide)]
  decide
#print axioms block40_entry0_1

theorem block40_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 397 i-2*unitVector 396 i)
      13 11 (-7) 399 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 198 399 (by decide),
      sourceChord_unit_even _ 198 399 (by decide)]
  decide
#print axioms block40_entry1_0

theorem block40_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 398 i-4*unitVector 396 i)
      13 11 (-7) 399 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 199 399 (by decide),
      sourceChord_unit_even _ 198 399 (by decide)]
  decide
#print axioms block40_entry1_1

theorem block41_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 399 i-8*unitVector 396 i)
      13 11 (-7) 401 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 199 401 (by decide),
      sourceChord_unit_even _ 198 401 (by decide)]
  decide
#print axioms block41_entry0_0

theorem block42_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 409 i-2*unitVector 408 i)
      13 11 (-7) 412 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 204 412 (by decide),
      sourceChord_unit_even _ 204 412 (by decide)]
  decide
#print axioms block42_entry0_0

theorem block43_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 411 i-8*unitVector 408 i)
      13 11 (-7) 413 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 205 413 (by decide),
      sourceChord_unit_even _ 204 413 (by decide)]
  decide
#print axioms block43_entry0_0

theorem block44_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 423 i-8*unitVector 420 i)
      13 11 (-7) 425 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 211 425 (by decide),
      sourceChord_unit_even _ 210 425 (by decide)]
  decide
#print axioms block44_entry0_0

theorem block44_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 425 i-2*unitVector 424 i)
      13 11 (-7) 425 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 212 425 (by decide),
      sourceChord_unit_even _ 212 425 (by decide)]
  decide
#print axioms block44_entry0_1

theorem block44_entry0_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 426 i-4*unitVector 424 i)
      13 11 (-7) 425 = 28 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 213 425 (by decide),
      sourceChord_unit_even _ 212 425 (by decide)]
  decide
#print axioms block44_entry0_2

theorem block44_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 423 i-8*unitVector 420 i)
      13 11 (-7) 427 = 0 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 211 427 (by decide),
      sourceChord_unit_even _ 210 427 (by decide)]
  decide
#print axioms block44_entry1_0

theorem block44_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 425 i-2*unitVector 424 i)
      13 11 (-7) 427 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 212 427 (by decide),
      sourceChord_unit_even _ 212 427 (by decide)]
  decide
#print axioms block44_entry1_1

theorem block44_entry1_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 426 i-4*unitVector 424 i)
      13 11 (-7) 427 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 213 427 (by decide),
      sourceChord_unit_even _ 212 427 (by decide)]
  decide
#print axioms block44_entry1_2

theorem block44_entry2_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 423 i-8*unitVector 420 i)
      13 11 (-7) 426 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 211 426 (by decide),
      sourceChord_unit_even _ 210 426 (by decide)]
  decide
#print axioms block44_entry2_0

theorem block44_entry2_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 425 i-2*unitVector 424 i)
      13 11 (-7) 426 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 212 426 (by decide),
      sourceChord_unit_even _ 212 426 (by decide)]
  decide
#print axioms block44_entry2_1

theorem block44_entry2_2 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 426 i-4*unitVector 424 i)
      13 11 (-7) 426 = 2147483616 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 213 426 (by decide),
      sourceChord_unit_even _ 212 426 (by decide)]
  decide
#print axioms block44_entry2_2

theorem block45_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 437 i-2*unitVector 436 i)
      13 11 (-7) 439 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 218 439 (by decide),
      sourceChord_unit_even _ 218 439 (by decide)]
  decide
#print axioms block45_entry0_0

theorem block46_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 449 i-2*unitVector 448 i)
      13 11 (-7) 451 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 224 451 (by decide),
      sourceChord_unit_even _ 224 451 (by decide)]
  decide
#print axioms block46_entry0_0

theorem block47_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 451 i-8*unitVector 448 i)
      13 11 (-7) 453 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 225 453 (by decide),
      sourceChord_unit_even _ 224 453 (by decide)]
  decide
#print axioms block47_entry0_0

theorem block48_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 461 i-2*unitVector 460 i)
      13 11 (-7) 464 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 230 464 (by decide),
      sourceChord_unit_even _ 230 464 (by decide)]
  decide
#print axioms block48_entry0_0

theorem block49_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 463 i-8*unitVector 460 i)
      13 11 (-7) 466 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 231 466 (by decide),
      sourceChord_unit_even _ 230 466 (by decide)]
  decide
#print axioms block49_entry0_0

theorem block49_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 465 i-2*unitVector 464 i)
      13 11 (-7) 466 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 232 466 (by decide),
      sourceChord_unit_even _ 232 466 (by decide)]
  decide
#print axioms block49_entry0_1

theorem block49_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 463 i-8*unitVector 460 i)
      13 11 (-7) 465 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 231 465 (by decide),
      sourceChord_unit_even _ 230 465 (by decide)]
  decide
#print axioms block49_entry1_0

theorem block49_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 465 i-2*unitVector 464 i)
      13 11 (-7) 465 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 232 465 (by decide),
      sourceChord_unit_even _ 232 465 (by decide)]
  decide
#print axioms block49_entry1_1

end AspisV8R17.SourceBlocks
