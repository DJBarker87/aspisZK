import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries02

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block19_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      154 154 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 244 114 = 1073741827
  unfold entry
  simp only [show 4*(22+114/3) = 240 from rfl,
    show 1+114%3 = 1 from rfl, show 240+1 = 241 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block19_entry0_0
#print axioms block19_entry0_0

theorem block19_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      154 155 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 244 115 = 1073741829
  unfold entry
  simp only [show 4*(22+115/3) = 240 from rfl,
    show 1+115%3 = 2 from rfl, show 240+2 = 242 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block19_entry0_1
#print axioms block19_entry0_1

theorem block19_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      155 154 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 243 114 = 11
  unfold entry
  simp only [show 4*(22+114/3) = 240 from rfl,
    show 1+114%3 = 1 from rfl, show 240+1 = 241 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block19_entry1_0
#print axioms block19_entry1_0

theorem block19_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      155 155 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 243 115 = 2147483640
  unfold entry
  simp only [show 4*(22+115/3) = 240 from rfl,
    show 1+115%3 = 2 from rfl, show 240+2 = 242 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block19_entry1_1
#print axioms block19_entry1_1

theorem block20_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      203 203 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 245 116 = 1073741829
  unfold entry
  simp only [show 4*(22+116/3) = 240 from rfl,
    show 1+116%3 = 3 from rfl, show 240+3 = 243 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block20_entry0_0
#print axioms block20_entry0_0

theorem block21_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      5 5 = 117440512 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 256 123 = 117440512
  unfold entry
  simp only [show 4*(22+123/3) = 252 from rfl,
    show 1+123%3 = 1 from rfl, show 252+1 = 253 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block21_entry0_0
#print axioms block21_entry0_0

theorem block22_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      128 128 = 117440512 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 258 125 = 117440512
  unfold entry
  simp only [show 4*(22+125/3) = 252 from rfl,
    show 1+125%3 = 3 from rfl, show 252+3 = 255 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block22_entry0_0
#print axioms block22_entry0_0

theorem block22_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      128 129 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 258 126 = 2147483625
  unfold entry
  simp only [show 4*(22+126/3) = 256 from rfl,
    show 1+126%3 = 1 from rfl, show 256+1 = 257 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block22_entry0_1
#print axioms block22_entry0_1

theorem block22_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      129 128 = 184549376 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 257 125 = 184549376
  unfold entry
  simp only [show 4*(22+125/3) = 252 from rfl,
    show 1+125%3 = 3 from rfl, show 252+3 = 255 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block22_entry1_0
#print axioms block22_entry1_0

theorem block22_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      129 129 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 257 126 = 27
  unfold entry
  simp only [show 4*(22+126/3) = 256 from rfl,
    show 1+126%3 = 1 from rfl, show 256+1 = 257 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block22_entry1_1
#print axioms block22_entry1_1

theorem block23_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      156 156 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 269 134 = 1073741829
  unfold entry
  simp only [show 4*(22+134/3) = 264 from rfl,
    show 1+134%3 = 3 from rfl, show 264+3 = 267 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block23_entry0_0
#print axioms block23_entry0_0

theorem block23_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      156 157 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 269 135 = 27
  unfold entry
  simp only [show 4*(22+135/3) = 268 from rfl,
    show 1+135%3 = 1 from rfl, show 268+1 = 269 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block23_entry0_1
#print axioms block23_entry0_1

theorem block23_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      156 158 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 269 136 = 28
  unfold entry
  simp only [show 4*(22+136/3) = 268 from rfl,
    show 1+136%3 = 2 from rfl, show 268+2 = 270 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block23_entry0_2
#print axioms block23_entry0_2

theorem block23_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      157 156 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 271 134 = 0
  unfold entry
  simp only [show 4*(22+134/3) = 264 from rfl,
    show 1+134%3 = 3 from rfl, show 264+3 = 267 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block23_entry1_0
#print axioms block23_entry1_0

theorem block23_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      157 157 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 271 135 = 11
  unfold entry
  simp only [show 4*(22+135/3) = 268 from rfl,
    show 1+135%3 = 1 from rfl, show 268+1 = 269 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block23_entry1_1
#print axioms block23_entry1_1

theorem block23_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      157 158 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 271 136 = 2147483640
  unfold entry
  simp only [show 4*(22+136/3) = 268 from rfl,
    show 1+136%3 = 2 from rfl, show 268+2 = 270 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block23_entry1_2
#print axioms block23_entry1_2

theorem block23_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      158 156 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 270 134 = 1073741827
  unfold entry
  simp only [show 4*(22+134/3) = 264 from rfl,
    show 1+134%3 = 3 from rfl, show 264+3 = 267 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block23_entry2_0
#print axioms block23_entry2_0

theorem block23_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      158 157 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 270 135 = 2147483625
  unfold entry
  simp only [show 4*(22+135/3) = 268 from rfl,
    show 1+135%3 = 1 from rfl, show 268+1 = 269 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block23_entry2_1
#print axioms block23_entry2_1

theorem block23_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      158 158 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 270 136 = 2147483616
  unfold entry
  simp only [show 4*(22+136/3) = 268 from rfl,
    show 1+136%3 = 2 from rfl, show 268+2 = 270 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block23_entry2_2
#print axioms block23_entry2_2

theorem block24_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      159 159 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 282 143 = 1610612737
  unfold entry
  simp only [show 4*(22+143/3) = 276 from rfl,
    show 1+143%3 = 3 from rfl, show 276+3 = 279 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block24_entry0_0
#print axioms block24_entry0_0

theorem block25_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      185 185 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 284 144 = 1073741827
  unfold entry
  simp only [show 4*(22+144/3) = 280 from rfl,
    show 1+144%3 = 1 from rfl, show 280+1 = 281 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block25_entry0_0
#print axioms block25_entry0_0

theorem block25_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      185 186 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 284 145 = 1073741829
  unfold entry
  simp only [show 4*(22+145/3) = 280 from rfl,
    show 1+145%3 = 2 from rfl, show 280+2 = 282 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block25_entry0_1
#print axioms block25_entry0_1

theorem block25_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      186 185 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 283 144 = 11
  unfold entry
  simp only [show 4*(22+144/3) = 280 from rfl,
    show 1+144%3 = 1 from rfl, show 280+1 = 281 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block25_entry1_0
#print axioms block25_entry1_0

theorem block25_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      186 186 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 283 145 = 2147483640
  unfold entry
  simp only [show 4*(22+145/3) = 280 from rfl,
    show 1+145%3 = 2 from rfl, show 280+2 = 282 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block25_entry1_1
#print axioms block25_entry1_1

theorem block26_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      160 160 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 296 153 = 1610612737
  unfold entry
  simp only [show 4*(22+153/3) = 292 from rfl,
    show 1+153%3 = 1 from rfl, show 292+1 = 293 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block26_entry0_0
#print axioms block26_entry0_0

theorem block26_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      160 161 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 296 154 = 1610612738
  unfold entry
  simp only [show 4*(22+154/3) = 292 from rfl,
    show 1+154%3 = 2 from rfl, show 292+2 = 294 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block26_entry0_1
#print axioms block26_entry0_1

theorem block26_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      161 160 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 295 153 = 11
  unfold entry
  simp only [show 4*(22+153/3) = 292 from rfl,
    show 1+153%3 = 1 from rfl, show 292+1 = 293 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block26_entry1_0
#print axioms block26_entry1_0

theorem block26_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      161 161 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 295 154 = 2147483640
  unfold entry
  simp only [show 4*(22+154/3) = 292 from rfl,
    show 1+154%3 = 2 from rfl, show 292+2 = 294 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block26_entry1_1
#print axioms block26_entry1_1

theorem block27_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      204 204 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 297 155 = 1610612738
  unfold entry
  simp only [show 4*(22+155/3) = 292 from rfl,
    show 1+155%3 = 3 from rfl, show 292+3 = 295 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block27_entry0_0
#print axioms block27_entry0_0

theorem block28_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      162 162 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 308 162 = 1073741827
  unfold entry
  simp only [show 4*(22+162/3) = 304 from rfl,
    show 1+162%3 = 1 from rfl, show 304+1 = 305 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block28_entry0_0
#print axioms block28_entry0_0

theorem block29_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      187 187 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 310 164 = 1073741827
  unfold entry
  simp only [show 4*(22+164/3) = 304 from rfl,
    show 1+164%3 = 3 from rfl, show 304+3 = 307 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block29_entry0_0
#print axioms block29_entry0_0

theorem block29_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      187 188 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 310 165 = 2147483625
  unfold entry
  simp only [show 4*(22+165/3) = 308 from rfl,
    show 1+165%3 = 1 from rfl, show 308+1 = 309 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block29_entry0_1
#print axioms block29_entry0_1

end AspisV8R17.SourceMinor.DiagonalBlocks
