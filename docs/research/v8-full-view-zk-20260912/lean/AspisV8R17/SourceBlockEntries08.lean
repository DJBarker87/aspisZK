import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block91_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 810 i-4*unitVector 808 i)
      13 11 (-7) 812 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 405 812 (by decide),
      sourceChord_unit_even _ 404 812 (by decide)]
  decide
#print axioms block91_entry0_1

theorem block91_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 809 i-2*unitVector 808 i)
      13 11 (-7) 811 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 404 811 (by decide),
      sourceChord_unit_even _ 404 811 (by decide)]
  decide
#print axioms block91_entry1_0

theorem block91_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 810 i-4*unitVector 808 i)
      13 11 (-7) 811 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 405 811 (by decide),
      sourceChord_unit_even _ 404 811 (by decide)]
  decide
#print axioms block91_entry1_1

theorem block92_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 813 i-2*unitVector 812 i)
      13 11 (-7) 816 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 406 816 (by decide),
      sourceChord_unit_even _ 406 816 (by decide)]
  decide
#print axioms block92_entry0_0

theorem block93_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 825 i-2*unitVector 824 i)
      13 11 (-7) 828 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 412 828 (by decide),
      sourceChord_unit_even _ 412 828 (by decide)]
  decide
#print axioms block93_entry0_0

theorem block93_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 826 i-4*unitVector 824 i)
      13 11 (-7) 828 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 413 828 (by decide),
      sourceChord_unit_even _ 412 828 (by decide)]
  decide
#print axioms block93_entry0_1

theorem block93_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 825 i-2*unitVector 824 i)
      13 11 (-7) 827 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 412 827 (by decide),
      sourceChord_unit_even _ 412 827 (by decide)]
  decide
#print axioms block93_entry1_0

theorem block93_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 826 i-4*unitVector 824 i)
      13 11 (-7) 827 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 413 827 (by decide),
      sourceChord_unit_even _ 412 827 (by decide)]
  decide
#print axioms block93_entry1_1

theorem block94_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 829 i-2*unitVector 828 i)
      13 11 (-7) 832 = 469762048 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 414 832 (by decide),
      sourceChord_unit_even _ 414 832 (by decide)]
  decide
#print axioms block94_entry0_0

theorem block95_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 841 i-2*unitVector 840 i)
      13 11 (-7) 844 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 420 844 (by decide),
      sourceChord_unit_even _ 420 844 (by decide)]
  decide
#print axioms block95_entry0_0

theorem block95_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 842 i-4*unitVector 840 i)
      13 11 (-7) 844 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 421 844 (by decide),
      sourceChord_unit_even _ 420 844 (by decide)]
  decide
#print axioms block95_entry0_1

theorem block95_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 841 i-2*unitVector 840 i)
      13 11 (-7) 843 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 420 843 (by decide),
      sourceChord_unit_even _ 420 843 (by decide)]
  decide
#print axioms block95_entry1_0

theorem block95_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 842 i-4*unitVector 840 i)
      13 11 (-7) 843 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 421 843 (by decide),
      sourceChord_unit_even _ 420 843 (by decide)]
  decide
#print axioms block95_entry1_1

theorem block96_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 845 i-2*unitVector 844 i)
      13 11 (-7) 848 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 422 848 (by decide),
      sourceChord_unit_even _ 422 848 (by decide)]
  decide
#print axioms block96_entry0_0

theorem block97_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 857 i-2*unitVector 856 i)
      13 11 (-7) 860 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 428 860 (by decide),
      sourceChord_unit_even _ 428 860 (by decide)]
  decide
#print axioms block97_entry0_0

theorem block98_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 861 i-2*unitVector 860 i)
      13 11 (-7) 864 = 939524096 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 430 864 (by decide),
      sourceChord_unit_even _ 430 864 (by decide)]
  decide
#print axioms block98_entry0_0

theorem block99_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 873 i-2*unitVector 872 i)
      13 11 (-7) 876 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 436 876 (by decide),
      sourceChord_unit_even _ 436 876 (by decide)]
  decide
#print axioms block99_entry0_0

theorem block99_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 874 i-4*unitVector 872 i)
      13 11 (-7) 876 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 437 876 (by decide),
      sourceChord_unit_even _ 436 876 (by decide)]
  decide
#print axioms block99_entry0_1

theorem block99_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 873 i-2*unitVector 872 i)
      13 11 (-7) 875 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 436 875 (by decide),
      sourceChord_unit_even _ 436 875 (by decide)]
  decide
#print axioms block99_entry1_0

theorem block99_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 874 i-4*unitVector 872 i)
      13 11 (-7) 875 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 437 875 (by decide),
      sourceChord_unit_even _ 436 875 (by decide)]
  decide
#print axioms block99_entry1_1

theorem block100_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 877 i-2*unitVector 876 i)
      13 11 (-7) 880 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 438 880 (by decide),
      sourceChord_unit_even _ 438 880 (by decide)]
  decide
#print axioms block100_entry0_0

theorem block101_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 889 i-2*unitVector 888 i)
      13 11 (-7) 892 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 444 892 (by decide),
      sourceChord_unit_even _ 444 892 (by decide)]
  decide
#print axioms block101_entry0_0

theorem block101_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 890 i-4*unitVector 888 i)
      13 11 (-7) 892 = 1073741829 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 445 892 (by decide),
      sourceChord_unit_even _ 444 892 (by decide)]
  decide
#print axioms block101_entry0_1

theorem block101_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 889 i-2*unitVector 888 i)
      13 11 (-7) 891 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 444 891 (by decide),
      sourceChord_unit_even _ 444 891 (by decide)]
  decide
#print axioms block101_entry1_0

theorem block101_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 890 i-4*unitVector 888 i)
      13 11 (-7) 891 = 2147483640 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_even _ 445 891 (by decide),
      sourceChord_unit_even _ 444 891 (by decide)]
  decide
#print axioms block101_entry1_1

theorem block102_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 893 i-2*unitVector 892 i)
      13 11 (-7) 896 = 234881024 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 446 896 (by decide),
      sourceChord_unit_even _ 446 896 (by decide)]
  decide
#print axioms block102_entry0_0

theorem block103_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 905 i-2*unitVector 904 i)
      13 11 (-7) 908 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 452 908 (by decide),
      sourceChord_unit_even _ 452 908 (by decide)]
  decide
#print axioms block103_entry0_0

theorem block104_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 911 i-8*unitVector 908 i)
      13 11 (-7) 914 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 455 914 (by decide),
      sourceChord_unit_even _ 454 914 (by decide)]
  decide
#print axioms block104_entry0_0

theorem block104_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 913 i-2*unitVector 912 i)
      13 11 (-7) 914 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 456 914 (by decide),
      sourceChord_unit_even _ 456 914 (by decide)]
  decide
#print axioms block104_entry0_1

theorem block104_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 911 i-8*unitVector 908 i)
      13 11 (-7) 913 = 805306369 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 455 913 (by decide),
      sourceChord_unit_even _ 454 913 (by decide)]
  decide
#print axioms block104_entry1_0

theorem block104_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 913 i-2*unitVector 912 i)
      13 11 (-7) 913 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 456 913 (by decide),
      sourceChord_unit_even _ 456 913 (by decide)]
  decide
#print axioms block104_entry1_1

theorem block105_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 915 i-8*unitVector 912 i)
      13 11 (-7) 918 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 457 918 (by decide),
      sourceChord_unit_even _ 456 918 (by decide)]
  decide
#print axioms block105_entry0_0

end AspisV8R17.SourceBlocks
