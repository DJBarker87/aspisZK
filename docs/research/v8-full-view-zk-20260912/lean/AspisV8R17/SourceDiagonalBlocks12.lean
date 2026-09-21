import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries12

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block128_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      136 136 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1010 689 = 1879048192
  unfold entry
  simp only [show 4*(22+689/3) = 1004 from rfl,
    show 1+689%3 = 3 from rfl, show 1004+3 = 1007 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block128_entry0_0
#print axioms block128_entry0_0

theorem block129_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      138 138 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1012 690 = 1073741827
  unfold entry
  simp only [show 4*(22+690/3) = 1008 from rfl,
    show 1+690%3 = 1 from rfl, show 1008+1 = 1009 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block129_entry0_0
#print axioms block129_entry0_0

theorem block130_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      139 139 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1014 692 = 1073741827
  unfold entry
  simp only [show 4*(22+692/3) = 1008 from rfl,
    show 1+692%3 = 3 from rfl, show 1008+3 = 1011 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block130_entry0_0
#print axioms block130_entry0_0

theorem block131_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      176 176 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1015 693 = 11
  unfold entry
  simp only [show 4*(22+693/3) = 1012 from rfl,
    show 1+693%3 = 1 from rfl, show 1012+1 = 1013 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block131_entry0_0
#print axioms block131_entry0_0

theorem block132_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      198 198 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1018 695 = 1610612737
  unfold entry
  simp only [show 4*(22+695/3) = 1012 from rfl,
    show 1+695%3 = 3 from rfl, show 1012+3 = 1015 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block132_entry0_0
#print axioms block132_entry0_0

theorem block132_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      198 199 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1018 696 = 2147483625
  unfold entry
  simp only [show 4*(22+696/3) = 1016 from rfl,
    show 1+696%3 = 1 from rfl, show 1016+1 = 1017 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block132_entry0_1
#print axioms block132_entry0_1

theorem block132_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      199 198 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1017 695 = 1610612738
  unfold entry
  simp only [show 4*(22+695/3) = 1012 from rfl,
    show 1+695%3 = 3 from rfl, show 1012+3 = 1015 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block132_entry1_0
#print axioms block132_entry1_0

theorem block132_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      199 199 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1017 696 = 27
  unfold entry
  simp only [show 4*(22+696/3) = 1016 from rfl,
    show 1+696%3 = 1 from rfl, show 1016+1 = 1017 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block132_entry1_1
#print axioms block132_entry1_1

end AspisV8R17.SourceMinor.DiagonalBlocks
