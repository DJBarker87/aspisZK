import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block50_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 475 i-8*unitVector 472 i)
      13 11 (-7) 477 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 237 477 (by decide),
      sourceChord_unit_even _ 236 477 (by decide)]
  decide
#print axioms block50_entry0_0

theorem block51_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 489 i-2*unitVector 488 i)
      13 11 (-7) 491 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 244 491 (by decide),
      sourceChord_unit_even _ 244 491 (by decide)]
  decide
#print axioms block51_entry0_0

theorem block52_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 493 i-2*unitVector 492 i)
      13 11 (-7) 496 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 246 496 (by decide),
      sourceChord_unit_even _ 246 496 (by decide)]
  decide
#print axioms block52_entry0_0

theorem block53_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 505 i-2*unitVector 504 i)
      13 11 (-7) 508 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 252 508 (by decide),
      sourceChord_unit_even _ 252 508 (by decide)]
  decide
#print axioms block53_entry0_0

theorem block53_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 506 i-4*unitVector 504 i)
      13 11 (-7) 508 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 253 508 (by decide),
      sourceChord_unit_even _ 252 508 (by decide)]
  decide
#print axioms block53_entry0_1

theorem block53_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 505 i-2*unitVector 504 i)
      13 11 (-7) 507 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 252 507 (by decide),
      sourceChord_unit_even _ 252 507 (by decide)]
  decide
#print axioms block53_entry1_0

theorem block53_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 506 i-4*unitVector 504 i)
      13 11 (-7) 507 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 253 507 (by decide),
      sourceChord_unit_even _ 252 507 (by decide)]
  decide
#print axioms block53_entry1_1

theorem block54_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 509 i-2*unitVector 508 i)
      13 11 (-7) 512 = 58720256 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 254 512 (by decide),
      sourceChord_unit_even _ 254 512 (by decide)]
  decide
#print axioms block54_entry0_0

theorem block55_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 521 i-2*unitVector 520 i)
      13 11 (-7) 523 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 260 523 (by decide),
      sourceChord_unit_even _ 260 523 (by decide)]
  decide
#print axioms block55_entry0_0

theorem block56_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 525 i-2*unitVector 524 i)
      13 11 (-7) 528 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 262 528 (by decide),
      sourceChord_unit_even _ 262 528 (by decide)]
  decide
#print axioms block56_entry0_0

theorem block57_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 537 i-2*unitVector 536 i)
      13 11 (-7) 540 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 268 540 (by decide),
      sourceChord_unit_even _ 268 540 (by decide)]
  decide
#print axioms block57_entry0_0

theorem block57_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 538 i-4*unitVector 536 i)
      13 11 (-7) 540 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 269 540 (by decide),
      sourceChord_unit_even _ 268 540 (by decide)]
  decide
#print axioms block57_entry0_1

theorem block57_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 537 i-2*unitVector 536 i)
      13 11 (-7) 539 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 268 539 (by decide),
      sourceChord_unit_even _ 268 539 (by decide)]
  decide
#print axioms block57_entry1_0

theorem block57_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 538 i-4*unitVector 536 i)
      13 11 (-7) 539 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 269 539 (by decide),
      sourceChord_unit_even _ 268 539 (by decide)]
  decide
#print axioms block57_entry1_1

theorem block58_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 541 i-2*unitVector 540 i)
      13 11 (-7) 544 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 270 544 (by decide),
      sourceChord_unit_even _ 270 544 (by decide)]
  decide
#print axioms block58_entry0_0

theorem block59_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 553 i-2*unitVector 552 i)
      13 11 (-7) 556 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 276 556 (by decide),
      sourceChord_unit_even _ 276 556 (by decide)]
  decide
#print axioms block59_entry0_0

theorem block59_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 554 i-4*unitVector 552 i)
      13 11 (-7) 556 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 277 556 (by decide),
      sourceChord_unit_even _ 276 556 (by decide)]
  decide
#print axioms block59_entry0_1

theorem block59_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 553 i-2*unitVector 552 i)
      13 11 (-7) 555 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 276 555 (by decide),
      sourceChord_unit_even _ 276 555 (by decide)]
  decide
#print axioms block59_entry1_0

theorem block59_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 554 i-4*unitVector 552 i)
      13 11 (-7) 555 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 277 555 (by decide),
      sourceChord_unit_even _ 276 555 (by decide)]
  decide
#print axioms block59_entry1_1

theorem block60_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 557 i-2*unitVector 556 i)
      13 11 (-7) 560 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 278 560 (by decide),
      sourceChord_unit_even _ 278 560 (by decide)]
  decide
#print axioms block60_entry0_0

theorem block61_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 569 i-2*unitVector 568 i)
      13 11 (-7) 572 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 284 572 (by decide),
      sourceChord_unit_even _ 284 572 (by decide)]
  decide
#print axioms block61_entry0_0

theorem block61_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 570 i-4*unitVector 568 i)
      13 11 (-7) 572 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 285 572 (by decide),
      sourceChord_unit_even _ 284 572 (by decide)]
  decide
#print axioms block61_entry0_1

theorem block61_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 569 i-2*unitVector 568 i)
      13 11 (-7) 571 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 284 571 (by decide),
      sourceChord_unit_even _ 284 571 (by decide)]
  decide
#print axioms block61_entry1_0

theorem block61_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 570 i-4*unitVector 568 i)
      13 11 (-7) 571 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 285 571 (by decide),
      sourceChord_unit_even _ 284 571 (by decide)]
  decide
#print axioms block61_entry1_1

theorem block62_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 573 i-2*unitVector 572 i)
      13 11 (-7) 576 = 469762048 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 286 576 (by decide),
      sourceChord_unit_even _ 286 576 (by decide)]
  decide
#print axioms block62_entry0_0

theorem block63_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 585 i-2*unitVector 584 i)
      13 11 (-7) 588 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 292 588 (by decide),
      sourceChord_unit_even _ 292 588 (by decide)]
  decide
#print axioms block63_entry0_0

theorem block63_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 586 i-4*unitVector 584 i)
      13 11 (-7) 588 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 293 588 (by decide),
      sourceChord_unit_even _ 292 588 (by decide)]
  decide
#print axioms block63_entry0_1

theorem block63_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 585 i-2*unitVector 584 i)
      13 11 (-7) 587 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 292 587 (by decide),
      sourceChord_unit_even _ 292 587 (by decide)]
  decide
#print axioms block63_entry1_0

theorem block63_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 586 i-4*unitVector 584 i)
      13 11 (-7) 587 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 293 587 (by decide),
      sourceChord_unit_even _ 292 587 (by decide)]
  decide
#print axioms block63_entry1_1

theorem block64_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 589 i-2*unitVector 588 i)
      13 11 (-7) 592 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 294 592 (by decide),
      sourceChord_unit_even _ 294 592 (by decide)]
  decide
#print axioms block64_entry0_0

theorem block65_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 601 i-2*unitVector 600 i)
      13 11 (-7) 604 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 300 604 (by decide),
      sourceChord_unit_even _ 300 604 (by decide)]
  decide
#print axioms block65_entry0_0

theorem block65_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 602 i-4*unitVector 600 i)
      13 11 (-7) 604 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 301 604 (by decide),
      sourceChord_unit_even _ 300 604 (by decide)]
  decide
#print axioms block65_entry0_1

end AspisV8R17.SourceBlocks
