import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block78_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 701 i-2*unitVector 700 i)
      13 11 (-7) 704 = 469762048 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 350 704 (by decide),
      sourceChord_unit_even _ 350 704 (by decide)]
  decide
#print axioms block78_entry0_0

theorem block79_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 713 i-2*unitVector 712 i)
      13 11 (-7) 716 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 356 716 (by decide),
      sourceChord_unit_even _ 356 716 (by decide)]
  decide
#print axioms block79_entry0_0

theorem block79_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 714 i-4*unitVector 712 i)
      13 11 (-7) 716 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 357 716 (by decide),
      sourceChord_unit_even _ 356 716 (by decide)]
  decide
#print axioms block79_entry0_1

theorem block79_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 713 i-2*unitVector 712 i)
      13 11 (-7) 715 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 356 715 (by decide),
      sourceChord_unit_even _ 356 715 (by decide)]
  decide
#print axioms block79_entry1_0

theorem block79_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 714 i-4*unitVector 712 i)
      13 11 (-7) 715 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 357 715 (by decide),
      sourceChord_unit_even _ 356 715 (by decide)]
  decide
#print axioms block79_entry1_1

theorem block80_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 717 i-2*unitVector 716 i)
      13 11 (-7) 720 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 358 720 (by decide),
      sourceChord_unit_even _ 358 720 (by decide)]
  decide
#print axioms block80_entry0_0

theorem block81_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 729 i-2*unitVector 728 i)
      13 11 (-7) 732 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 364 732 (by decide),
      sourceChord_unit_even _ 364 732 (by decide)]
  decide
#print axioms block81_entry0_0

theorem block81_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 730 i-4*unitVector 728 i)
      13 11 (-7) 732 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 365 732 (by decide),
      sourceChord_unit_even _ 364 732 (by decide)]
  decide
#print axioms block81_entry0_1

theorem block81_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 729 i-2*unitVector 728 i)
      13 11 (-7) 731 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 364 731 (by decide),
      sourceChord_unit_even _ 364 731 (by decide)]
  decide
#print axioms block81_entry1_0

theorem block81_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 730 i-4*unitVector 728 i)
      13 11 (-7) 731 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 365 731 (by decide),
      sourceChord_unit_even _ 364 731 (by decide)]
  decide
#print axioms block81_entry1_1

theorem block82_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 733 i-2*unitVector 732 i)
      13 11 (-7) 736 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 366 736 (by decide),
      sourceChord_unit_even _ 366 736 (by decide)]
  decide
#print axioms block82_entry0_0

theorem block83_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 745 i-2*unitVector 744 i)
      13 11 (-7) 748 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 372 748 (by decide),
      sourceChord_unit_even _ 372 748 (by decide)]
  decide
#print axioms block83_entry0_0

theorem block83_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 746 i-4*unitVector 744 i)
      13 11 (-7) 748 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 373 748 (by decide),
      sourceChord_unit_even _ 372 748 (by decide)]
  decide
#print axioms block83_entry0_1

theorem block83_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 745 i-2*unitVector 744 i)
      13 11 (-7) 747 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 372 747 (by decide),
      sourceChord_unit_even _ 372 747 (by decide)]
  decide
#print axioms block83_entry1_0

theorem block83_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 746 i-4*unitVector 744 i)
      13 11 (-7) 747 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 373 747 (by decide),
      sourceChord_unit_even _ 372 747 (by decide)]
  decide
#print axioms block83_entry1_1

theorem block84_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 749 i-2*unitVector 748 i)
      13 11 (-7) 752 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 374 752 (by decide),
      sourceChord_unit_even _ 374 752 (by decide)]
  decide
#print axioms block84_entry0_0

theorem block85_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 761 i-2*unitVector 760 i)
      13 11 (-7) 764 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 380 764 (by decide),
      sourceChord_unit_even _ 380 764 (by decide)]
  decide
#print axioms block85_entry0_0

theorem block85_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 762 i-4*unitVector 760 i)
      13 11 (-7) 764 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 381 764 (by decide),
      sourceChord_unit_even _ 380 764 (by decide)]
  decide
#print axioms block85_entry0_1

theorem block85_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 761 i-2*unitVector 760 i)
      13 11 (-7) 763 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 380 763 (by decide),
      sourceChord_unit_even _ 380 763 (by decide)]
  decide
#print axioms block85_entry1_0

theorem block85_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 762 i-4*unitVector 760 i)
      13 11 (-7) 763 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 381 763 (by decide),
      sourceChord_unit_even _ 380 763 (by decide)]
  decide
#print axioms block85_entry1_1

theorem block86_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 765 i-2*unitVector 764 i)
      13 11 (-7) 768 = 117440512 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 382 768 (by decide),
      sourceChord_unit_even _ 382 768 (by decide)]
  decide
#print axioms block86_entry0_0

theorem block87_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 777 i-2*unitVector 776 i)
      13 11 (-7) 780 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 388 780 (by decide),
      sourceChord_unit_even _ 388 780 (by decide)]
  decide
#print axioms block87_entry0_0

theorem block87_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 778 i-4*unitVector 776 i)
      13 11 (-7) 780 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 389 780 (by decide),
      sourceChord_unit_even _ 388 780 (by decide)]
  decide
#print axioms block87_entry0_1

theorem block87_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 777 i-2*unitVector 776 i)
      13 11 (-7) 779 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 388 779 (by decide),
      sourceChord_unit_even _ 388 779 (by decide)]
  decide
#print axioms block87_entry1_0

theorem block87_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 778 i-4*unitVector 776 i)
      13 11 (-7) 779 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 389 779 (by decide),
      sourceChord_unit_even _ 388 779 (by decide)]
  decide
#print axioms block87_entry1_1

theorem block88_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 781 i-2*unitVector 780 i)
      13 11 (-7) 784 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 390 784 (by decide),
      sourceChord_unit_even _ 390 784 (by decide)]
  decide
#print axioms block88_entry0_0

theorem block89_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 793 i-2*unitVector 792 i)
      13 11 (-7) 796 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 396 796 (by decide),
      sourceChord_unit_even _ 396 796 (by decide)]
  decide
#print axioms block89_entry0_0

theorem block89_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 794 i-4*unitVector 792 i)
      13 11 (-7) 796 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 397 796 (by decide),
      sourceChord_unit_even _ 396 796 (by decide)]
  decide
#print axioms block89_entry0_1

theorem block89_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 793 i-2*unitVector 792 i)
      13 11 (-7) 795 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 396 795 (by decide),
      sourceChord_unit_even _ 396 795 (by decide)]
  decide
#print axioms block89_entry1_0

theorem block89_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 794 i-4*unitVector 792 i)
      13 11 (-7) 795 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 397 795 (by decide),
      sourceChord_unit_even _ 396 795 (by decide)]
  decide
#print axioms block89_entry1_1

theorem block90_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 797 i-2*unitVector 796 i)
      13 11 (-7) 800 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 398 800 (by decide),
      sourceChord_unit_even _ 398 800 (by decide)]
  decide
#print axioms block90_entry0_0

theorem block91_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 809 i-2*unitVector 808 i)
      13 11 (-7) 812 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 404 812 (by decide),
      sourceChord_unit_even _ 404 812 (by decide)]
  decide
#print axioms block91_entry0_0

end AspisV8R17.SourceBlocks
