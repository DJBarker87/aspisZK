import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block65_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 601 i-2*unitVector 600 i)
      13 11 (-7) 603 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 300 603 (by decide),
      sourceChord_unit_even _ 300 603 (by decide)]
  decide
#print axioms block65_entry1_0

theorem block65_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 602 i-4*unitVector 600 i)
      13 11 (-7) 603 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 301 603 (by decide),
      sourceChord_unit_even _ 300 603 (by decide)]
  decide
#print axioms block65_entry1_1

theorem block66_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 605 i-2*unitVector 604 i)
      13 11 (-7) 608 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 302 608 (by decide),
      sourceChord_unit_even _ 302 608 (by decide)]
  decide
#print axioms block66_entry0_0

theorem block67_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 617 i-2*unitVector 616 i)
      13 11 (-7) 620 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 308 620 (by decide),
      sourceChord_unit_even _ 308 620 (by decide)]
  decide
#print axioms block67_entry0_0

theorem block67_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 618 i-4*unitVector 616 i)
      13 11 (-7) 620 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 309 620 (by decide),
      sourceChord_unit_even _ 308 620 (by decide)]
  decide
#print axioms block67_entry0_1

theorem block67_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 617 i-2*unitVector 616 i)
      13 11 (-7) 619 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 308 619 (by decide),
      sourceChord_unit_even _ 308 619 (by decide)]
  decide
#print axioms block67_entry1_0

theorem block67_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 618 i-4*unitVector 616 i)
      13 11 (-7) 619 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 309 619 (by decide),
      sourceChord_unit_even _ 308 619 (by decide)]
  decide
#print axioms block67_entry1_1

theorem block68_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 621 i-2*unitVector 620 i)
      13 11 (-7) 624 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 310 624 (by decide),
      sourceChord_unit_even _ 310 624 (by decide)]
  decide
#print axioms block68_entry0_0

theorem block69_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 633 i-2*unitVector 632 i)
      13 11 (-7) 636 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 316 636 (by decide),
      sourceChord_unit_even _ 316 636 (by decide)]
  decide
#print axioms block69_entry0_0

theorem block69_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 634 i-4*unitVector 632 i)
      13 11 (-7) 636 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 317 636 (by decide),
      sourceChord_unit_even _ 316 636 (by decide)]
  decide
#print axioms block69_entry0_1

theorem block69_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 633 i-2*unitVector 632 i)
      13 11 (-7) 635 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 316 635 (by decide),
      sourceChord_unit_even _ 316 635 (by decide)]
  decide
#print axioms block69_entry1_0

theorem block69_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 634 i-4*unitVector 632 i)
      13 11 (-7) 635 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 317 635 (by decide),
      sourceChord_unit_even _ 316 635 (by decide)]
  decide
#print axioms block69_entry1_1

theorem block70_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 637 i-2*unitVector 636 i)
      13 11 (-7) 640 = 234881024 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 318 640 (by decide),
      sourceChord_unit_even _ 318 640 (by decide)]
  decide
#print axioms block70_entry0_0

theorem block71_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 649 i-2*unitVector 648 i)
      13 11 (-7) 652 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 324 652 (by decide),
      sourceChord_unit_even _ 324 652 (by decide)]
  decide
#print axioms block71_entry0_0

theorem block71_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 650 i-4*unitVector 648 i)
      13 11 (-7) 652 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 325 652 (by decide),
      sourceChord_unit_even _ 324 652 (by decide)]
  decide
#print axioms block71_entry0_1

theorem block71_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 649 i-2*unitVector 648 i)
      13 11 (-7) 651 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 324 651 (by decide),
      sourceChord_unit_even _ 324 651 (by decide)]
  decide
#print axioms block71_entry1_0

theorem block71_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 650 i-4*unitVector 648 i)
      13 11 (-7) 651 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 325 651 (by decide),
      sourceChord_unit_even _ 324 651 (by decide)]
  decide
#print axioms block71_entry1_1

theorem block72_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 653 i-2*unitVector 652 i)
      13 11 (-7) 656 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 326 656 (by decide),
      sourceChord_unit_even _ 326 656 (by decide)]
  decide
#print axioms block72_entry0_0

theorem block73_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 665 i-2*unitVector 664 i)
      13 11 (-7) 668 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 332 668 (by decide),
      sourceChord_unit_even _ 332 668 (by decide)]
  decide
#print axioms block73_entry0_0

theorem block73_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 666 i-4*unitVector 664 i)
      13 11 (-7) 668 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 333 668 (by decide),
      sourceChord_unit_even _ 332 668 (by decide)]
  decide
#print axioms block73_entry0_1

theorem block73_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 665 i-2*unitVector 664 i)
      13 11 (-7) 667 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 332 667 (by decide),
      sourceChord_unit_even _ 332 667 (by decide)]
  decide
#print axioms block73_entry1_0

theorem block73_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 666 i-4*unitVector 664 i)
      13 11 (-7) 667 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 333 667 (by decide),
      sourceChord_unit_even _ 332 667 (by decide)]
  decide
#print axioms block73_entry1_1

theorem block74_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 669 i-2*unitVector 668 i)
      13 11 (-7) 672 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 334 672 (by decide),
      sourceChord_unit_even _ 334 672 (by decide)]
  decide
#print axioms block74_entry0_0

theorem block75_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 681 i-2*unitVector 680 i)
      13 11 (-7) 684 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 340 684 (by decide),
      sourceChord_unit_even _ 340 684 (by decide)]
  decide
#print axioms block75_entry0_0

theorem block75_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 682 i-4*unitVector 680 i)
      13 11 (-7) 684 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 341 684 (by decide),
      sourceChord_unit_even _ 340 684 (by decide)]
  decide
#print axioms block75_entry0_1

theorem block75_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 681 i-2*unitVector 680 i)
      13 11 (-7) 683 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 340 683 (by decide),
      sourceChord_unit_even _ 340 683 (by decide)]
  decide
#print axioms block75_entry1_0

theorem block75_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 682 i-4*unitVector 680 i)
      13 11 (-7) 683 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 341 683 (by decide),
      sourceChord_unit_even _ 340 683 (by decide)]
  decide
#print axioms block75_entry1_1

theorem block76_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 685 i-2*unitVector 684 i)
      13 11 (-7) 688 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 342 688 (by decide),
      sourceChord_unit_even _ 342 688 (by decide)]
  decide
#print axioms block76_entry0_0

theorem block77_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 697 i-2*unitVector 696 i)
      13 11 (-7) 700 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 348 700 (by decide),
      sourceChord_unit_even _ 348 700 (by decide)]
  decide
#print axioms block77_entry0_0

theorem block77_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 698 i-4*unitVector 696 i)
      13 11 (-7) 700 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 349 700 (by decide),
      sourceChord_unit_even _ 348 700 (by decide)]
  decide
#print axioms block77_entry0_1

theorem block77_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 697 i-2*unitVector 696 i)
      13 11 (-7) 699 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 348 699 (by decide),
      sourceChord_unit_even _ 348 699 (by decide)]
  decide
#print axioms block77_entry1_0

theorem block77_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 698 i-4*unitVector 696 i)
      13 11 (-7) 699 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 349 699 (by decide),
      sourceChord_unit_even _ 348 699 (by decide)]
  decide
#print axioms block77_entry1_1

end AspisV8R17.SourceBlocks
