import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries00

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block0_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      200 200 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 100 6 = 1073741827
  unfold entry
  simp only [show 4*(22+6/3) = 96 from rfl,
    show 1+6%3 = 1 from rfl, show 96+1 = 97 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block0_entry0_0
#print axioms block0_entry0_0

theorem block1_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      201 201 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 101 8 = 1073741829
  unfold entry
  simp only [show 4*(22+8/3) = 96 from rfl,
    show 1+8%3 = 3 from rfl, show 96+3 = 99 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block1_entry0_0
#print axioms block1_entry0_0

theorem block2_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      140 140 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 113 17 = 805306369
  unfold entry
  simp only [show 4*(22+17/3) = 108 from rfl,
    show 1+17%3 = 3 from rfl, show 108+3 = 111 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block2_entry0_0
#print axioms block2_entry0_0

theorem block2_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      140 141 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 113 18 = 27
  unfold entry
  simp only [show 4*(22+18/3) = 112 from rfl,
    show 1+18%3 = 1 from rfl, show 112+1 = 113 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block2_entry0_1
#print axioms block2_entry0_1

theorem block2_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      140 142 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 113 19 = 28
  unfold entry
  simp only [show 4*(22+19/3) = 112 from rfl,
    show 1+19%3 = 2 from rfl, show 112+2 = 114 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block2_entry0_2
#print axioms block2_entry0_2

theorem block2_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      141 140 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 115 17 = 0
  unfold entry
  simp only [show 4*(22+17/3) = 108 from rfl,
    show 1+17%3 = 3 from rfl, show 108+3 = 111 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block2_entry1_0
#print axioms block2_entry1_0

theorem block2_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      141 141 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 115 18 = 11
  unfold entry
  simp only [show 4*(22+18/3) = 112 from rfl,
    show 1+18%3 = 1 from rfl, show 112+1 = 113 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block2_entry1_1
#print axioms block2_entry1_1

theorem block2_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      141 142 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 115 19 = 2147483640
  unfold entry
  simp only [show 4*(22+19/3) = 112 from rfl,
    show 1+19%3 = 2 from rfl, show 112+2 = 114 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block2_entry1_2
#print axioms block2_entry1_2

theorem block2_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      142 140 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 114 17 = 1879048192
  unfold entry
  simp only [show 4*(22+17/3) = 108 from rfl,
    show 1+17%3 = 3 from rfl, show 108+3 = 111 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block2_entry2_0
#print axioms block2_entry2_0

theorem block2_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      142 141 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 114 18 = 2147483625
  unfold entry
  simp only [show 4*(22+18/3) = 112 from rfl,
    show 1+18%3 = 1 from rfl, show 112+1 = 113 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block2_entry2_1
#print axioms block2_entry2_1

theorem block2_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      142 142 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 114 19 = 2147483616
  unfold entry
  simp only [show 4*(22+19/3) = 112 from rfl,
    show 1+19%3 = 2 from rfl, show 112+2 = 114 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block2_entry2_2
#print axioms block2_entry2_2

theorem block3_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      0 0 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 126 26 = 1073741827
  unfold entry
  simp only [show 4*(22+26/3) = 120 from rfl,
    show 1+26%3 = 3 from rfl, show 120+3 = 123 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block3_entry0_0
#print axioms block3_entry0_0

theorem block4_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      1 1 = 234881024 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 128 27 = 234881024
  unfold entry
  simp only [show 4*(22+27/3) = 124 from rfl,
    show 1+27%3 = 1 from rfl, show 124+1 = 125 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block4_entry0_0
#print axioms block4_entry0_0

theorem block4_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      1 2 = 369098752 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 128 28 = 369098752
  unfold entry
  simp only [show 4*(22+28/3) = 124 from rfl,
    show 1+28%3 = 2 from rfl, show 124+2 = 126 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block4_entry0_1
#print axioms block4_entry0_1

theorem block4_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      2 1 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 127 27 = 11
  unfold entry
  simp only [show 4*(22+27/3) = 124 from rfl,
    show 1+27%3 = 1 from rfl, show 124+1 = 125 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block4_entry1_0
#print axioms block4_entry1_0

theorem block4_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      2 2 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 127 28 = 2147483640
  unfold entry
  simp only [show 4*(22+28/3) = 124 from rfl,
    show 1+28%3 = 2 from rfl, show 124+2 = 126 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block4_entry1_1
#print axioms block4_entry1_1

theorem block5_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      143 143 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 140 36 = 1073741827
  unfold entry
  simp only [show 4*(22+36/3) = 136 from rfl,
    show 1+36%3 = 1 from rfl, show 136+1 = 137 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block5_entry0_0
#print axioms block5_entry0_0

theorem block5_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      143 144 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 140 37 = 1073741829
  unfold entry
  simp only [show 4*(22+37/3) = 136 from rfl,
    show 1+37%3 = 2 from rfl, show 136+2 = 138 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block5_entry0_1
#print axioms block5_entry0_1

theorem block5_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      144 143 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 139 36 = 11
  unfold entry
  simp only [show 4*(22+36/3) = 136 from rfl,
    show 1+36%3 = 1 from rfl, show 136+1 = 137 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block5_entry1_0
#print axioms block5_entry1_0

theorem block5_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      144 144 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 139 37 = 2147483640
  unfold entry
  simp only [show 4*(22+37/3) = 136 from rfl,
    show 1+37%3 = 2 from rfl, show 136+2 = 138 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block5_entry1_1
#print axioms block5_entry1_1

theorem block6_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      202 202 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 141 38 = 1073741829
  unfold entry
  simp only [show 4*(22+38/3) = 136 from rfl,
    show 1+38%3 = 3 from rfl, show 136+3 = 139 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block6_entry0_0
#print axioms block6_entry0_0

theorem block7_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      145 145 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 152 45 = 1610612737
  unfold entry
  simp only [show 4*(22+45/3) = 148 from rfl,
    show 1+45%3 = 1 from rfl, show 148+1 = 149 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block7_entry0_0
#print axioms block7_entry0_0

theorem block8_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      177 177 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 154 47 = 1610612737
  unfold entry
  simp only [show 4*(22+47/3) = 148 from rfl,
    show 1+47%3 = 3 from rfl, show 148+3 = 151 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block8_entry0_0
#print axioms block8_entry0_0

theorem block8_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      177 178 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 154 48 = 2147483625
  unfold entry
  simp only [show 4*(22+48/3) = 152 from rfl,
    show 1+48%3 = 1 from rfl, show 152+1 = 153 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block8_entry0_1
#print axioms block8_entry0_1

theorem block8_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      178 177 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 153 47 = 1610612738
  unfold entry
  simp only [show 4*(22+47/3) = 148 from rfl,
    show 1+47%3 = 3 from rfl, show 148+3 = 151 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block8_entry1_0
#print axioms block8_entry1_0

theorem block8_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      178 178 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 153 48 = 27
  unfold entry
  simp only [show 4*(22+48/3) = 152 from rfl,
    show 1+48%3 = 1 from rfl, show 152+1 = 153 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block8_entry1_1
#print axioms block8_entry1_1

theorem block9_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      146 146 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 165 56 = 1073741829
  unfold entry
  simp only [show 4*(22+56/3) = 160 from rfl,
    show 1+56%3 = 3 from rfl, show 160+3 = 163 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block9_entry0_0
#print axioms block9_entry0_0

theorem block9_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      146 147 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 165 57 = 27
  unfold entry
  simp only [show 4*(22+57/3) = 164 from rfl,
    show 1+57%3 = 1 from rfl, show 164+1 = 165 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block9_entry0_1
#print axioms block9_entry0_1

theorem block9_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      146 148 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 165 58 = 28
  unfold entry
  simp only [show 4*(22+58/3) = 164 from rfl,
    show 1+58%3 = 2 from rfl, show 164+2 = 166 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block9_entry0_2
#print axioms block9_entry0_2

theorem block9_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      147 146 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 167 56 = 0
  unfold entry
  simp only [show 4*(22+56/3) = 160 from rfl,
    show 1+56%3 = 3 from rfl, show 160+3 = 163 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block9_entry1_0
#print axioms block9_entry1_0

theorem block9_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      147 147 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 167 57 = 11
  unfold entry
  simp only [show 4*(22+57/3) = 164 from rfl,
    show 1+57%3 = 1 from rfl, show 164+1 = 165 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block9_entry1_1
#print axioms block9_entry1_1

theorem block9_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      147 148 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 167 58 = 2147483640
  unfold entry
  simp only [show 4*(22+58/3) = 164 from rfl,
    show 1+58%3 = 2 from rfl, show 164+2 = 166 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block9_entry1_2
#print axioms block9_entry1_2

end AspisV8R17.SourceMinor.DiagonalBlocks
