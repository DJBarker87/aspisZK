import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries03

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block29_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      188 187 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 309 164 = 1073741829
  unfold entry
  simp only [show 4*(22+164/3) = 304 from rfl,
    show 1+164%3 = 3 from rfl, show 304+3 = 307 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block29_entry1_0
#print axioms block29_entry1_0

theorem block29_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      188 188 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 309 165 = 27
  unfold entry
  simp only [show 4*(22+165/3) = 308 from rfl,
    show 1+165%3 = 1 from rfl, show 308+1 = 309 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block29_entry1_1
#print axioms block29_entry1_1

theorem block30_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      133 133 = 738197504 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 321 173 = 738197504
  unfold entry
  simp only [show 4*(22+173/3) = 316 from rfl,
    show 1+173%3 = 3 from rfl, show 316+3 = 319 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block30_entry0_0
#print axioms block30_entry0_0

theorem block30_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      133 134 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 321 174 = 27
  unfold entry
  simp only [show 4*(22+174/3) = 320 from rfl,
    show 1+174%3 = 1 from rfl, show 320+1 = 321 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block30_entry0_1
#print axioms block30_entry0_1

theorem block30_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      133 135 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 321 175 = 28
  unfold entry
  simp only [show 4*(22+175/3) = 320 from rfl,
    show 1+175%3 = 2 from rfl, show 320+2 = 322 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block30_entry0_2
#print axioms block30_entry0_2

theorem block30_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      134 133 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 323 173 = 0
  unfold entry
  simp only [show 4*(22+173/3) = 316 from rfl,
    show 1+173%3 = 3 from rfl, show 316+3 = 319 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block30_entry1_0
#print axioms block30_entry1_0

theorem block30_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      134 134 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 323 174 = 11
  unfold entry
  simp only [show 4*(22+174/3) = 320 from rfl,
    show 1+174%3 = 1 from rfl, show 320+1 = 321 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block30_entry1_1
#print axioms block30_entry1_1

theorem block30_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      134 135 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 323 175 = 2147483640
  unfold entry
  simp only [show 4*(22+175/3) = 320 from rfl,
    show 1+175%3 = 2 from rfl, show 320+2 = 322 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block30_entry1_2
#print axioms block30_entry1_2

theorem block30_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      135 133 = 469762048 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 322 173 = 469762048
  unfold entry
  simp only [show 4*(22+173/3) = 316 from rfl,
    show 1+173%3 = 3 from rfl, show 316+3 = 319 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block30_entry2_0
#print axioms block30_entry2_0

theorem block30_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      135 134 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 322 174 = 2147483625
  unfold entry
  simp only [show 4*(22+174/3) = 320 from rfl,
    show 1+174%3 = 1 from rfl, show 320+1 = 321 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block30_entry2_1
#print axioms block30_entry2_1

theorem block30_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      135 135 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 322 175 = 2147483616
  unfold entry
  simp only [show 4*(22+175/3) = 320 from rfl,
    show 1+175%3 = 2 from rfl, show 320+2 = 322 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block30_entry2_2
#print axioms block30_entry2_2

theorem block31_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      163 163 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 334 182 = 1073741827
  unfold entry
  simp only [show 4*(22+182/3) = 328 from rfl,
    show 1+182%3 = 3 from rfl, show 328+3 = 331 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block31_entry0_0
#print axioms block31_entry0_0

theorem block32_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      189 189 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 336 183 = 1879048192
  unfold entry
  simp only [show 4*(22+183/3) = 332 from rfl,
    show 1+183%3 = 1 from rfl, show 332+1 = 333 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block32_entry0_0
#print axioms block32_entry0_0

theorem block32_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      189 190 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 336 184 = 805306369
  unfold entry
  simp only [show 4*(22+184/3) = 332 from rfl,
    show 1+184%3 = 2 from rfl, show 332+2 = 334 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block32_entry0_1
#print axioms block32_entry0_1

theorem block32_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      190 189 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 335 183 = 11
  unfold entry
  simp only [show 4*(22+183/3) = 332 from rfl,
    show 1+183%3 = 1 from rfl, show 332+1 = 333 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block32_entry1_0
#print axioms block32_entry1_0

theorem block32_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      190 190 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 335 184 = 2147483640
  unfold entry
  simp only [show 4*(22+184/3) = 332 from rfl,
    show 1+184%3 = 2 from rfl, show 332+2 = 334 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block32_entry1_1
#print axioms block32_entry1_1

theorem block33_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      164 164 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 348 192 = 1073741827
  unfold entry
  simp only [show 4*(22+192/3) = 344 from rfl,
    show 1+192%3 = 1 from rfl, show 344+1 = 345 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block33_entry0_0
#print axioms block33_entry0_0

theorem block33_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      164 165 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 348 193 = 1073741829
  unfold entry
  simp only [show 4*(22+193/3) = 344 from rfl,
    show 1+193%3 = 2 from rfl, show 344+2 = 346 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block33_entry0_1
#print axioms block33_entry0_1

theorem block33_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      165 164 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 347 192 = 11
  unfold entry
  simp only [show 4*(22+192/3) = 344 from rfl,
    show 1+192%3 = 1 from rfl, show 344+1 = 345 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block33_entry1_0
#print axioms block33_entry1_0

theorem block33_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      165 165 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 347 193 = 2147483640
  unfold entry
  simp only [show 4*(22+193/3) = 344 from rfl,
    show 1+193%3 = 2 from rfl, show 344+2 = 346 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block33_entry1_1
#print axioms block33_entry1_1

theorem block34_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      205 205 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 349 194 = 1073741829
  unfold entry
  simp only [show 4*(22+194/3) = 344 from rfl,
    show 1+194%3 = 3 from rfl, show 344+3 = 347 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block34_entry0_0
#print axioms block34_entry0_0

theorem block35_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      166 166 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 360 201 = 1610612737
  unfold entry
  simp only [show 4*(22+201/3) = 356 from rfl,
    show 1+201%3 = 1 from rfl, show 356+1 = 357 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block35_entry0_0
#print axioms block35_entry0_0

theorem block36_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      191 191 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 362 203 = 1610612737
  unfold entry
  simp only [show 4*(22+203/3) = 356 from rfl,
    show 1+203%3 = 3 from rfl, show 356+3 = 359 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block36_entry0_0
#print axioms block36_entry0_0

theorem block36_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      191 192 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 362 204 = 2147483625
  unfold entry
  simp only [show 4*(22+204/3) = 360 from rfl,
    show 1+204%3 = 1 from rfl, show 360+1 = 361 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block36_entry0_1
#print axioms block36_entry0_1

theorem block36_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      192 191 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 361 203 = 1610612738
  unfold entry
  simp only [show 4*(22+203/3) = 356 from rfl,
    show 1+203%3 = 3 from rfl, show 356+3 = 359 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block36_entry1_0
#print axioms block36_entry1_0

theorem block36_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      192 192 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 361 204 = 27
  unfold entry
  simp only [show 4*(22+204/3) = 360 from rfl,
    show 1+204%3 = 1 from rfl, show 360+1 = 361 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block36_entry1_1
#print axioms block36_entry1_1

theorem block37_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      167 167 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 373 212 = 1073741829
  unfold entry
  simp only [show 4*(22+212/3) = 368 from rfl,
    show 1+212%3 = 3 from rfl, show 368+3 = 371 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block37_entry0_0
#print axioms block37_entry0_0

theorem block37_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      167 168 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 373 213 = 27
  unfold entry
  simp only [show 4*(22+213/3) = 372 from rfl,
    show 1+213%3 = 1 from rfl, show 372+1 = 373 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block37_entry0_1
#print axioms block37_entry0_1

theorem block37_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      167 169 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 373 214 = 28
  unfold entry
  simp only [show 4*(22+214/3) = 372 from rfl,
    show 1+214%3 = 2 from rfl, show 372+2 = 374 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block37_entry0_2
#print axioms block37_entry0_2

theorem block37_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      168 167 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 375 212 = 0
  unfold entry
  simp only [show 4*(22+212/3) = 368 from rfl,
    show 1+212%3 = 3 from rfl, show 368+3 = 371 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block37_entry1_0
#print axioms block37_entry1_0

theorem block37_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      168 168 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 375 213 = 11
  unfold entry
  simp only [show 4*(22+213/3) = 372 from rfl,
    show 1+213%3 = 1 from rfl, show 372+1 = 373 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block37_entry1_1
#print axioms block37_entry1_1

theorem block37_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      168 169 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 375 214 = 2147483640
  unfold entry
  simp only [show 4*(22+214/3) = 372 from rfl,
    show 1+214%3 = 2 from rfl, show 372+2 = 374 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block37_entry1_2
#print axioms block37_entry1_2

end AspisV8R17.SourceMinor.DiagonalBlocks
