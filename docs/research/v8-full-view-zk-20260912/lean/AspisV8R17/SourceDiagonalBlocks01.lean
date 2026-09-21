import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries01

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block9_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      148 146 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 166 56 = 1073741827
  unfold entry
  simp only [show 4*(22+56/3) = 160 from rfl,
    show 1+56%3 = 3 from rfl, show 160+3 = 163 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block9_entry2_0
#print axioms block9_entry2_0

theorem block9_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      148 147 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 166 57 = 2147483625
  unfold entry
  simp only [show 4*(22+57/3) = 164 from rfl,
    show 1+57%3 = 1 from rfl, show 164+1 = 165 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block9_entry2_1
#print axioms block9_entry2_1

theorem block9_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      148 148 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 166 58 = 2147483616
  unfold entry
  simp only [show 4*(22+58/3) = 164 from rfl,
    show 1+58%3 = 2 from rfl, show 164+2 = 166 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block9_entry2_2
#print axioms block9_entry2_2

theorem block10_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      122 122 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 178 65 = 1879048192
  unfold entry
  simp only [show 4*(22+65/3) = 172 from rfl,
    show 1+65%3 = 3 from rfl, show 172+3 = 175 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block10_entry0_0
#print axioms block10_entry0_0

theorem block11_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      179 179 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 180 66 = 1073741827
  unfold entry
  simp only [show 4*(22+66/3) = 176 from rfl,
    show 1+66%3 = 1 from rfl, show 176+1 = 177 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block11_entry0_0
#print axioms block11_entry0_0

theorem block11_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      179 180 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 180 67 = 1073741829
  unfold entry
  simp only [show 4*(22+67/3) = 176 from rfl,
    show 1+67%3 = 2 from rfl, show 176+2 = 178 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block11_entry0_1
#print axioms block11_entry0_1

theorem block11_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      180 179 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 179 66 = 11
  unfold entry
  simp only [show 4*(22+66/3) = 176 from rfl,
    show 1+66%3 = 1 from rfl, show 176+1 = 177 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block11_entry1_0
#print axioms block11_entry1_0

theorem block11_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      180 180 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 179 67 = 2147483640
  unfold entry
  simp only [show 4*(22+67/3) = 176 from rfl,
    show 1+67%3 = 2 from rfl, show 176+2 = 178 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block11_entry1_1
#print axioms block11_entry1_1

theorem block12_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      3 3 = 469762048 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 192 75 = 469762048
  unfold entry
  simp only [show 4*(22+75/3) = 188 from rfl,
    show 1+75%3 = 1 from rfl, show 188+1 = 189 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block12_entry0_0
#print axioms block12_entry0_0

theorem block12_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      3 4 = 738197504 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 192 76 = 738197504
  unfold entry
  simp only [show 4*(22+76/3) = 188 from rfl,
    show 1+76%3 = 2 from rfl, show 188+2 = 190 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block12_entry0_1
#print axioms block12_entry0_1

theorem block12_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      4 3 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 191 75 = 11
  unfold entry
  simp only [show 4*(22+75/3) = 188 from rfl,
    show 1+75%3 = 1 from rfl, show 188+1 = 189 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block12_entry1_0
#print axioms block12_entry1_0

theorem block12_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      4 4 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 191 76 = 2147483640
  unfold entry
  simp only [show 4*(22+76/3) = 188 from rfl,
    show 1+76%3 = 2 from rfl, show 188+2 = 190 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block12_entry1_1
#print axioms block12_entry1_1

theorem block13_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      127 127 = 738197504 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 193 77 = 738197504
  unfold entry
  simp only [show 4*(22+77/3) = 188 from rfl,
    show 1+77%3 = 3 from rfl, show 188+3 = 191 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block13_entry0_0
#print axioms block13_entry0_0

theorem block14_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      149 149 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 204 84 = 1073741827
  unfold entry
  simp only [show 4*(22+84/3) = 200 from rfl,
    show 1+84%3 = 1 from rfl, show 200+1 = 201 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block14_entry0_0
#print axioms block14_entry0_0

theorem block15_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      181 181 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 206 86 = 1073741827
  unfold entry
  simp only [show 4*(22+86/3) = 200 from rfl,
    show 1+86%3 = 3 from rfl, show 200+3 = 203 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block15_entry0_0
#print axioms block15_entry0_0

theorem block15_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      181 182 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 206 87 = 2147483625
  unfold entry
  simp only [show 4*(22+87/3) = 204 from rfl,
    show 1+87%3 = 1 from rfl, show 204+1 = 205 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block15_entry0_1
#print axioms block15_entry0_1

theorem block15_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      182 181 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 205 86 = 1073741829
  unfold entry
  simp only [show 4*(22+86/3) = 200 from rfl,
    show 1+86%3 = 3 from rfl, show 200+3 = 203 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block15_entry1_0
#print axioms block15_entry1_0

theorem block15_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      182 182 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 205 87 = 27
  unfold entry
  simp only [show 4*(22+87/3) = 204 from rfl,
    show 1+87%3 = 1 from rfl, show 204+1 = 205 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block15_entry1_1
#print axioms block15_entry1_1

theorem block16_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      150 150 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 217 95 = 1610612738
  unfold entry
  simp only [show 4*(22+95/3) = 212 from rfl,
    show 1+95%3 = 3 from rfl, show 212+3 = 215 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block16_entry0_0
#print axioms block16_entry0_0

theorem block16_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      150 151 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 217 96 = 27
  unfold entry
  simp only [show 4*(22+96/3) = 216 from rfl,
    show 1+96%3 = 1 from rfl, show 216+1 = 217 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block16_entry0_1
#print axioms block16_entry0_1

theorem block16_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      150 152 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 217 97 = 28
  unfold entry
  simp only [show 4*(22+97/3) = 216 from rfl,
    show 1+97%3 = 2 from rfl, show 216+2 = 218 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block16_entry0_2
#print axioms block16_entry0_2

theorem block16_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      151 150 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 219 95 = 0
  unfold entry
  simp only [show 4*(22+95/3) = 212 from rfl,
    show 1+95%3 = 3 from rfl, show 212+3 = 215 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block16_entry1_0
#print axioms block16_entry1_0

theorem block16_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      151 151 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 219 96 = 11
  unfold entry
  simp only [show 4*(22+96/3) = 216 from rfl,
    show 1+96%3 = 1 from rfl, show 216+1 = 217 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block16_entry1_1
#print axioms block16_entry1_1

theorem block16_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      151 152 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 219 97 = 2147483640
  unfold entry
  simp only [show 4*(22+97/3) = 216 from rfl,
    show 1+97%3 = 2 from rfl, show 216+2 = 218 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block16_entry1_2
#print axioms block16_entry1_2

theorem block16_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      152 150 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 218 95 = 1610612737
  unfold entry
  simp only [show 4*(22+95/3) = 212 from rfl,
    show 1+95%3 = 3 from rfl, show 212+3 = 215 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block16_entry2_0
#print axioms block16_entry2_0

theorem block16_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      152 151 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 218 96 = 2147483625
  unfold entry
  simp only [show 4*(22+96/3) = 216 from rfl,
    show 1+96%3 = 1 from rfl, show 216+1 = 217 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block16_entry2_1
#print axioms block16_entry2_1

theorem block16_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      152 152 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 218 97 = 2147483616
  unfold entry
  simp only [show 4*(22+97/3) = 216 from rfl,
    show 1+97%3 = 2 from rfl, show 216+2 = 218 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block16_entry2_2
#print axioms block16_entry2_2

theorem block17_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      153 153 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 230 104 = 1073741827
  unfold entry
  simp only [show 4*(22+104/3) = 224 from rfl,
    show 1+104%3 = 3 from rfl, show 224+3 = 227 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block17_entry0_0
#print axioms block17_entry0_0

theorem block18_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      183 183 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 232 105 = 1610612737
  unfold entry
  simp only [show 4*(22+105/3) = 228 from rfl,
    show 1+105%3 = 1 from rfl, show 228+1 = 229 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block18_entry0_0
#print axioms block18_entry0_0

theorem block18_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      183 184 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 232 106 = 1610612738
  unfold entry
  simp only [show 4*(22+106/3) = 228 from rfl,
    show 1+106%3 = 2 from rfl, show 228+2 = 230 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block18_entry0_1
#print axioms block18_entry0_1

theorem block18_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      184 183 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 231 105 = 11
  unfold entry
  simp only [show 4*(22+105/3) = 228 from rfl,
    show 1+105%3 = 1 from rfl, show 228+1 = 229 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block18_entry1_0
#print axioms block18_entry1_0

theorem block18_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      184 184 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 231 106 = 2147483640
  unfold entry
  simp only [show 4*(22+106/3) = 228 from rfl,
    show 1+106%3 = 2 from rfl, show 228+2 = 230 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block18_entry1_1
#print axioms block18_entry1_1

end AspisV8R17.SourceMinor.DiagonalBlocks
