import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! Generated sparse source-model block entries. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses named sparse rewrites; never unfolds the full source edge list. -/
set_option autoImplicit false
namespace AspisV8R17.SourceBlocks
theorem block128_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1007 i-8*unitVector 1004 i)
      13 11 (-7) 1010 = 1879048192 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 503 1010 (by decide),
      sourceChord_unit_even _ 502 1010 (by decide)]
  decide
#print axioms block128_entry0_0

theorem block129_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1009 i-2*unitVector 1008 i)
      13 11 (-7) 1012 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 504 1012 (by decide),
      sourceChord_unit_even _ 504 1012 (by decide)]
  decide
#print axioms block129_entry0_0

theorem block130_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1011 i-8*unitVector 1008 i)
      13 11 (-7) 1014 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 505 1014 (by decide),
      sourceChord_unit_even _ 504 1014 (by decide)]
  decide
#print axioms block130_entry0_0

theorem block131_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1013 i-2*unitVector 1012 i)
      13 11 (-7) 1015 = 11 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 506 1015 (by decide),
      sourceChord_unit_even _ 506 1015 (by decide)]
  decide
#print axioms block131_entry0_0

theorem block132_entry0_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1015 i-8*unitVector 1012 i)
      13 11 (-7) 1018 = 1610612737 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 507 1018 (by decide),
      sourceChord_unit_even _ 506 1018 (by decide)]
  decide
#print axioms block132_entry0_0

theorem block132_entry0_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1017 i-2*unitVector 1016 i)
      13 11 (-7) 1018 = 2147483625 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 508 1018 (by decide),
      sourceChord_unit_even _ 508 1018 (by decide)]
  decide
#print axioms block132_entry0_1

theorem block132_entry1_0 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1015 i-8*unitVector 1012 i)
      13 11 (-7) 1017 = 1610612738 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 507 1017 (by decide),
      sourceChord_unit_even _ 506 1017 (by decide)]
  decide
#print axioms block132_entry1_0

theorem block132_entry1_1 :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 1017 i-2*unitVector 1016 i)
      13 11 (-7) 1017 = 27 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 508 1017 (by decide),
      sourceChord_unit_even _ 508 1017 (by decide)]
  decide
#print axioms block132_entry1_1

end AspisV8R17.SourceBlocks
