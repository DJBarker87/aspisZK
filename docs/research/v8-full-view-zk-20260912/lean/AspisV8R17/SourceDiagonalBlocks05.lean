import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries05

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block50_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      211 211 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 477 290 = 1073741829
  unfold entry
  simp only [show 4*(22+290/3) = 472 from rfl,
    show 1+290%3 = 3 from rfl, show 472+3 = 475 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block50_entry0_0
#print axioms block50_entry0_0

theorem block51_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      212 212 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 491 300 = 11
  unfold entry
  simp only [show 4*(22+300/3) = 488 from rfl,
    show 1+300%3 = 1 from rfl, show 488+1 = 489 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block51_entry0_0
#print axioms block51_entry0_0

theorem block52_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      8 8 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 496 303 = 1879048192
  unfold entry
  simp only [show 4*(22+303/3) = 492 from rfl,
    show 1+303%3 = 1 from rfl, show 492+1 = 493 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block52_entry0_0
#print axioms block52_entry0_0

theorem block53_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      6 6 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 508 312 = 1073741827
  unfold entry
  simp only [show 4*(22+312/3) = 504 from rfl,
    show 1+312%3 = 1 from rfl, show 504+1 = 505 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block53_entry0_0
#print axioms block53_entry0_0

theorem block53_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      6 7 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 508 313 = 1073741829
  unfold entry
  simp only [show 4*(22+313/3) = 504 from rfl,
    show 1+313%3 = 2 from rfl, show 504+2 = 506 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block53_entry0_1
#print axioms block53_entry0_1

theorem block53_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      7 6 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 507 312 = 11
  unfold entry
  simp only [show 4*(22+312/3) = 504 from rfl,
    show 1+312%3 = 1 from rfl, show 504+1 = 505 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block53_entry1_0
#print axioms block53_entry1_0

theorem block53_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      7 7 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 507 313 = 2147483640
  unfold entry
  simp only [show 4*(22+313/3) = 504 from rfl,
    show 1+313%3 = 2 from rfl, show 504+2 = 506 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block53_entry1_1
#print axioms block53_entry1_1

theorem block54_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      9 9 = 58720256 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 512 315 = 58720256
  unfold entry
  simp only [show 4*(22+315/3) = 508 from rfl,
    show 1+315%3 = 1 from rfl, show 508+1 = 509 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block54_entry0_0
#print axioms block54_entry0_0

theorem block55_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      213 213 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 523 324 = 11
  unfold entry
  simp only [show 4*(22+324/3) = 520 from rfl,
    show 1+324%3 = 1 from rfl, show 520+1 = 521 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block55_entry0_0
#print axioms block55_entry0_0

theorem block56_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      12 12 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 528 327 = 1879048192
  unfold entry
  simp only [show 4*(22+327/3) = 524 from rfl,
    show 1+327%3 = 1 from rfl, show 524+1 = 525 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block56_entry0_0
#print axioms block56_entry0_0

theorem block57_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      10 10 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 540 336 = 1073741827
  unfold entry
  simp only [show 4*(22+336/3) = 536 from rfl,
    show 1+336%3 = 1 from rfl, show 536+1 = 537 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block57_entry0_0
#print axioms block57_entry0_0

theorem block57_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      10 11 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 540 337 = 1073741829
  unfold entry
  simp only [show 4*(22+337/3) = 536 from rfl,
    show 1+337%3 = 2 from rfl, show 536+2 = 538 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block57_entry0_1
#print axioms block57_entry0_1

theorem block57_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      11 10 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 539 336 = 11
  unfold entry
  simp only [show 4*(22+336/3) = 536 from rfl,
    show 1+336%3 = 1 from rfl, show 536+1 = 537 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block57_entry1_0
#print axioms block57_entry1_0

theorem block57_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      11 11 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 539 337 = 2147483640
  unfold entry
  simp only [show 4*(22+337/3) = 536 from rfl,
    show 1+337%3 = 2 from rfl, show 536+2 = 538 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block57_entry1_1
#print axioms block57_entry1_1

theorem block58_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      15 15 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 544 339 = 939524096
  unfold entry
  simp only [show 4*(22+339/3) = 540 from rfl,
    show 1+339%3 = 1 from rfl, show 540+1 = 541 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block58_entry0_0
#print axioms block58_entry0_0

theorem block59_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      13 13 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 556 348 = 1073741827
  unfold entry
  simp only [show 4*(22+348/3) = 552 from rfl,
    show 1+348%3 = 1 from rfl, show 552+1 = 553 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block59_entry0_0
#print axioms block59_entry0_0

theorem block59_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      13 14 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 556 349 = 1073741829
  unfold entry
  simp only [show 4*(22+349/3) = 552 from rfl,
    show 1+349%3 = 2 from rfl, show 552+2 = 554 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block59_entry0_1
#print axioms block59_entry0_1

theorem block59_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      14 13 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 555 348 = 11
  unfold entry
  simp only [show 4*(22+348/3) = 552 from rfl,
    show 1+348%3 = 1 from rfl, show 552+1 = 553 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block59_entry1_0
#print axioms block59_entry1_0

theorem block59_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      14 14 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 555 349 = 2147483640
  unfold entry
  simp only [show 4*(22+349/3) = 552 from rfl,
    show 1+349%3 = 2 from rfl, show 552+2 = 554 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block59_entry1_1
#print axioms block59_entry1_1

theorem block60_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      18 18 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 560 351 = 1879048192
  unfold entry
  simp only [show 4*(22+351/3) = 556 from rfl,
    show 1+351%3 = 1 from rfl, show 556+1 = 557 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block60_entry0_0
#print axioms block60_entry0_0

theorem block61_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      16 16 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 572 360 = 1073741827
  unfold entry
  simp only [show 4*(22+360/3) = 568 from rfl,
    show 1+360%3 = 1 from rfl, show 568+1 = 569 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block61_entry0_0
#print axioms block61_entry0_0

theorem block61_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      16 17 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 572 361 = 1073741829
  unfold entry
  simp only [show 4*(22+361/3) = 568 from rfl,
    show 1+361%3 = 2 from rfl, show 568+2 = 570 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block61_entry0_1
#print axioms block61_entry0_1

theorem block61_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      17 16 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 571 360 = 11
  unfold entry
  simp only [show 4*(22+360/3) = 568 from rfl,
    show 1+360%3 = 1 from rfl, show 568+1 = 569 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block61_entry1_0
#print axioms block61_entry1_0

theorem block61_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      17 17 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 571 361 = 2147483640
  unfold entry
  simp only [show 4*(22+361/3) = 568 from rfl,
    show 1+361%3 = 2 from rfl, show 568+2 = 570 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block61_entry1_1
#print axioms block61_entry1_1

theorem block62_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      21 21 = 469762048 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 576 363 = 469762048
  unfold entry
  simp only [show 4*(22+363/3) = 572 from rfl,
    show 1+363%3 = 1 from rfl, show 572+1 = 573 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block62_entry0_0
#print axioms block62_entry0_0

theorem block63_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      19 19 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 588 372 = 1073741827
  unfold entry
  simp only [show 4*(22+372/3) = 584 from rfl,
    show 1+372%3 = 1 from rfl, show 584+1 = 585 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block63_entry0_0
#print axioms block63_entry0_0

theorem block63_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      19 20 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 588 373 = 1073741829
  unfold entry
  simp only [show 4*(22+373/3) = 584 from rfl,
    show 1+373%3 = 2 from rfl, show 584+2 = 586 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block63_entry0_1
#print axioms block63_entry0_1

theorem block63_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      20 19 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 587 372 = 11
  unfold entry
  simp only [show 4*(22+372/3) = 584 from rfl,
    show 1+372%3 = 1 from rfl, show 584+1 = 585 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block63_entry1_0
#print axioms block63_entry1_0

theorem block63_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      20 20 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 587 373 = 2147483640
  unfold entry
  simp only [show 4*(22+373/3) = 584 from rfl,
    show 1+373%3 = 2 from rfl, show 584+2 = 586 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block63_entry1_1
#print axioms block63_entry1_1

theorem block64_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      24 24 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 592 375 = 1879048192
  unfold entry
  simp only [show 4*(22+375/3) = 588 from rfl,
    show 1+375%3 = 1 from rfl, show 588+1 = 589 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block64_entry0_0
#print axioms block64_entry0_0

theorem block65_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      22 22 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 604 384 = 1073741827
  unfold entry
  simp only [show 4*(22+384/3) = 600 from rfl,
    show 1+384%3 = 1 from rfl, show 600+1 = 601 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block65_entry0_0
#print axioms block65_entry0_0

theorem block65_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      22 23 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 604 385 = 1073741829
  unfold entry
  simp only [show 4*(22+385/3) = 600 from rfl,
    show 1+385%3 = 2 from rfl, show 600+2 = 602 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block65_entry0_1
#print axioms block65_entry0_1

end AspisV8R17.SourceMinor.DiagonalBlocks
