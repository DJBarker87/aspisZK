import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries04

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block37_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      169 167 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 374 212 = 1073741827
  unfold entry
  simp only [show 4*(22+212/3) = 368 from rfl,
    show 1+212%3 = 3 from rfl, show 368+3 = 371 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block37_entry2_0
#print axioms block37_entry2_0

theorem block37_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      169 168 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 374 213 = 2147483625
  unfold entry
  simp only [show 4*(22+213/3) = 372 from rfl,
    show 1+213%3 = 1 from rfl, show 372+1 = 373 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block37_entry2_1
#print axioms block37_entry2_1

theorem block37_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      169 169 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 374 214 = 2147483616
  unfold entry
  simp only [show 4*(22+214/3) = 372 from rfl,
    show 1+214%3 = 2 from rfl, show 372+2 = 374 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block37_entry2_2
#print axioms block37_entry2_2

theorem block38_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      137 137 = 234881024 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 386 221 = 234881024
  unfold entry
  simp only [show 4*(22+221/3) = 380 from rfl,
    show 1+221%3 = 3 from rfl, show 380+3 = 383 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block38_entry0_0
#print axioms block38_entry0_0

theorem block39_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      193 193 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 388 222 = 1073741827
  unfold entry
  simp only [show 4*(22+222/3) = 384 from rfl,
    show 1+222%3 = 1 from rfl, show 384+1 = 385 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block39_entry0_0
#print axioms block39_entry0_0

theorem block39_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      193 194 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 388 223 = 1073741829
  unfold entry
  simp only [show 4*(22+223/3) = 384 from rfl,
    show 1+223%3 = 2 from rfl, show 384+2 = 386 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block39_entry0_1
#print axioms block39_entry0_1

theorem block39_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      194 193 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 387 222 = 11
  unfold entry
  simp only [show 4*(22+222/3) = 384 from rfl,
    show 1+222%3 = 1 from rfl, show 384+1 = 385 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block39_entry1_0
#print axioms block39_entry1_0

theorem block39_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      194 194 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 387 223 = 2147483640
  unfold entry
  simp only [show 4*(22+223/3) = 384 from rfl,
    show 1+223%3 = 2 from rfl, show 384+2 = 386 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block39_entry1_1
#print axioms block39_entry1_1

theorem block40_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      170 170 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 400 231 = 1879048192
  unfold entry
  simp only [show 4*(22+231/3) = 396 from rfl,
    show 1+231%3 = 1 from rfl, show 396+1 = 397 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block40_entry0_0
#print axioms block40_entry0_0

theorem block40_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      170 171 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 400 232 = 805306369
  unfold entry
  simp only [show 4*(22+232/3) = 396 from rfl,
    show 1+232%3 = 2 from rfl, show 396+2 = 398 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block40_entry0_1
#print axioms block40_entry0_1

theorem block40_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      171 170 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 399 231 = 11
  unfold entry
  simp only [show 4*(22+231/3) = 396 from rfl,
    show 1+231%3 = 1 from rfl, show 396+1 = 397 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block40_entry1_0
#print axioms block40_entry1_0

theorem block40_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      171 171 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 399 232 = 2147483640
  unfold entry
  simp only [show 4*(22+232/3) = 396 from rfl,
    show 1+232%3 = 2 from rfl, show 396+2 = 398 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block40_entry1_1
#print axioms block40_entry1_1

theorem block41_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      206 206 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 401 233 = 805306369
  unfold entry
  simp only [show 4*(22+233/3) = 396 from rfl,
    show 1+233%3 = 3 from rfl, show 396+3 = 399 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block41_entry0_0
#print axioms block41_entry0_0

theorem block42_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      207 207 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 412 240 = 1073741827
  unfold entry
  simp only [show 4*(22+240/3) = 408 from rfl,
    show 1+240%3 = 1 from rfl, show 408+1 = 409 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block42_entry0_0
#print axioms block42_entry0_0

theorem block43_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      208 208 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 413 242 = 1073741829
  unfold entry
  simp only [show 4*(22+242/3) = 408 from rfl,
    show 1+242%3 = 3 from rfl, show 408+3 = 411 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block43_entry0_0
#print axioms block43_entry0_0

theorem block44_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      172 172 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 425 251 = 1610612738
  unfold entry
  simp only [show 4*(22+251/3) = 420 from rfl,
    show 1+251%3 = 3 from rfl, show 420+3 = 423 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block44_entry0_0
#print axioms block44_entry0_0

theorem block44_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      172 173 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 425 252 = 27
  unfold entry
  simp only [show 4*(22+252/3) = 424 from rfl,
    show 1+252%3 = 1 from rfl, show 424+1 = 425 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block44_entry0_1
#print axioms block44_entry0_1

theorem block44_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      172 174 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 425 253 = 28
  unfold entry
  simp only [show 4*(22+253/3) = 424 from rfl,
    show 1+253%3 = 2 from rfl, show 424+2 = 426 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block44_entry0_2
#print axioms block44_entry0_2

theorem block44_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      173 172 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 427 251 = 0
  unfold entry
  simp only [show 4*(22+251/3) = 420 from rfl,
    show 1+251%3 = 3 from rfl, show 420+3 = 423 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block44_entry1_0
#print axioms block44_entry1_0

theorem block44_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      173 173 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 427 252 = 11
  unfold entry
  simp only [show 4*(22+252/3) = 424 from rfl,
    show 1+252%3 = 1 from rfl, show 424+1 = 425 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block44_entry1_1
#print axioms block44_entry1_1

theorem block44_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      173 174 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 427 253 = 2147483640
  unfold entry
  simp only [show 4*(22+253/3) = 424 from rfl,
    show 1+253%3 = 2 from rfl, show 424+2 = 426 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block44_entry1_2
#print axioms block44_entry1_2

theorem block44_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      174 172 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 426 251 = 1610612737
  unfold entry
  simp only [show 4*(22+251/3) = 420 from rfl,
    show 1+251%3 = 3 from rfl, show 420+3 = 423 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block44_entry2_0
#print axioms block44_entry2_0

theorem block44_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      174 173 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 426 252 = 2147483625
  unfold entry
  simp only [show 4*(22+252/3) = 424 from rfl,
    show 1+252%3 = 1 from rfl, show 424+1 = 425 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block44_entry2_1
#print axioms block44_entry2_1

theorem block44_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      174 174 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 426 253 = 2147483616
  unfold entry
  simp only [show 4*(22+253/3) = 424 from rfl,
    show 1+253%3 = 2 from rfl, show 424+2 = 426 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block44_entry2_2
#print axioms block44_entry2_2

theorem block45_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      209 209 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 439 261 = 11
  unfold entry
  simp only [show 4*(22+261/3) = 436 from rfl,
    show 1+261%3 = 1 from rfl, show 436+1 = 437 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block45_entry0_0
#print axioms block45_entry0_0

theorem block46_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      195 195 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 451 270 = 11
  unfold entry
  simp only [show 4*(22+270/3) = 448 from rfl,
    show 1+270%3 = 1 from rfl, show 448+1 = 449 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block46_entry0_0
#print axioms block46_entry0_0

theorem block47_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      210 210 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 453 272 = 1073741829
  unfold entry
  simp only [show 4*(22+272/3) = 448 from rfl,
    show 1+272%3 = 3 from rfl, show 448+3 = 451 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block47_entry0_0
#print axioms block47_entry0_0

theorem block48_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      175 175 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 464 279 = 1879048192
  unfold entry
  simp only [show 4*(22+279/3) = 460 from rfl,
    show 1+279%3 = 1 from rfl, show 460+1 = 461 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block48_entry0_0
#print axioms block48_entry0_0

theorem block49_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      196 196 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 466 281 = 1879048192
  unfold entry
  simp only [show 4*(22+281/3) = 460 from rfl,
    show 1+281%3 = 3 from rfl, show 460+3 = 463 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block49_entry0_0
#print axioms block49_entry0_0

theorem block49_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      196 197 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 466 282 = 2147483625
  unfold entry
  simp only [show 4*(22+282/3) = 464 from rfl,
    show 1+282%3 = 1 from rfl, show 464+1 = 465 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block49_entry0_1
#print axioms block49_entry0_1

theorem block49_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      197 196 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 465 281 = 805306369
  unfold entry
  simp only [show 4*(22+281/3) = 460 from rfl,
    show 1+281%3 = 3 from rfl, show 460+3 = 463 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block49_entry1_0
#print axioms block49_entry1_0

theorem block49_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      197 197 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 465 282 = 27
  unfold entry
  simp only [show 4*(22+282/3) = 464 from rfl,
    show 1+282%3 = 1 from rfl, show 464+1 = 465 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block49_entry1_1
#print axioms block49_entry1_1

end AspisV8R17.SourceMinor.DiagonalBlocks
