import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries06

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block65_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      23 22 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 603 384 = 11
  unfold entry
  simp only [show 4*(22+384/3) = 600 from rfl,
    show 1+384%3 = 1 from rfl, show 600+1 = 601 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block65_entry1_0
#print axioms block65_entry1_0

theorem block65_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      23 23 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 603 385 = 2147483640
  unfold entry
  simp only [show 4*(22+385/3) = 600 from rfl,
    show 1+385%3 = 2 from rfl, show 600+2 = 602 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block65_entry1_1
#print axioms block65_entry1_1

theorem block66_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      27 27 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 608 387 = 939524096
  unfold entry
  simp only [show 4*(22+387/3) = 604 from rfl,
    show 1+387%3 = 1 from rfl, show 604+1 = 605 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block66_entry0_0
#print axioms block66_entry0_0

theorem block67_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      25 25 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 620 396 = 1073741827
  unfold entry
  simp only [show 4*(22+396/3) = 616 from rfl,
    show 1+396%3 = 1 from rfl, show 616+1 = 617 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block67_entry0_0
#print axioms block67_entry0_0

theorem block67_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      25 26 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 620 397 = 1073741829
  unfold entry
  simp only [show 4*(22+397/3) = 616 from rfl,
    show 1+397%3 = 2 from rfl, show 616+2 = 618 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block67_entry0_1
#print axioms block67_entry0_1

theorem block67_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      26 25 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 619 396 = 11
  unfold entry
  simp only [show 4*(22+396/3) = 616 from rfl,
    show 1+396%3 = 1 from rfl, show 616+1 = 617 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block67_entry1_0
#print axioms block67_entry1_0

theorem block67_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      26 26 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 619 397 = 2147483640
  unfold entry
  simp only [show 4*(22+397/3) = 616 from rfl,
    show 1+397%3 = 2 from rfl, show 616+2 = 618 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block67_entry1_1
#print axioms block67_entry1_1

theorem block68_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      30 30 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 624 399 = 1879048192
  unfold entry
  simp only [show 4*(22+399/3) = 620 from rfl,
    show 1+399%3 = 1 from rfl, show 620+1 = 621 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block68_entry0_0
#print axioms block68_entry0_0

theorem block69_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      28 28 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 636 408 = 1073741827
  unfold entry
  simp only [show 4*(22+408/3) = 632 from rfl,
    show 1+408%3 = 1 from rfl, show 632+1 = 633 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block69_entry0_0
#print axioms block69_entry0_0

theorem block69_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      28 29 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 636 409 = 1073741829
  unfold entry
  simp only [show 4*(22+409/3) = 632 from rfl,
    show 1+409%3 = 2 from rfl, show 632+2 = 634 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block69_entry0_1
#print axioms block69_entry0_1

theorem block69_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      29 28 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 635 408 = 11
  unfold entry
  simp only [show 4*(22+408/3) = 632 from rfl,
    show 1+408%3 = 1 from rfl, show 632+1 = 633 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block69_entry1_0
#print axioms block69_entry1_0

theorem block69_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      29 29 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 635 409 = 2147483640
  unfold entry
  simp only [show 4*(22+409/3) = 632 from rfl,
    show 1+409%3 = 2 from rfl, show 632+2 = 634 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block69_entry1_1
#print axioms block69_entry1_1

theorem block70_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      33 33 = 234881024 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 640 411 = 234881024
  unfold entry
  simp only [show 4*(22+411/3) = 636 from rfl,
    show 1+411%3 = 1 from rfl, show 636+1 = 637 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block70_entry0_0
#print axioms block70_entry0_0

theorem block71_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      31 31 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 652 420 = 1073741827
  unfold entry
  simp only [show 4*(22+420/3) = 648 from rfl,
    show 1+420%3 = 1 from rfl, show 648+1 = 649 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block71_entry0_0
#print axioms block71_entry0_0

theorem block71_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      31 32 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 652 421 = 1073741829
  unfold entry
  simp only [show 4*(22+421/3) = 648 from rfl,
    show 1+421%3 = 2 from rfl, show 648+2 = 650 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block71_entry0_1
#print axioms block71_entry0_1

theorem block71_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      32 31 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 651 420 = 11
  unfold entry
  simp only [show 4*(22+420/3) = 648 from rfl,
    show 1+420%3 = 1 from rfl, show 648+1 = 649 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block71_entry1_0
#print axioms block71_entry1_0

theorem block71_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      32 32 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 651 421 = 2147483640
  unfold entry
  simp only [show 4*(22+421/3) = 648 from rfl,
    show 1+421%3 = 2 from rfl, show 648+2 = 650 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block71_entry1_1
#print axioms block71_entry1_1

theorem block72_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      36 36 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 656 423 = 1879048192
  unfold entry
  simp only [show 4*(22+423/3) = 652 from rfl,
    show 1+423%3 = 1 from rfl, show 652+1 = 653 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block72_entry0_0
#print axioms block72_entry0_0

theorem block73_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      34 34 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 668 432 = 1073741827
  unfold entry
  simp only [show 4*(22+432/3) = 664 from rfl,
    show 1+432%3 = 1 from rfl, show 664+1 = 665 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block73_entry0_0
#print axioms block73_entry0_0

theorem block73_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      34 35 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 668 433 = 1073741829
  unfold entry
  simp only [show 4*(22+433/3) = 664 from rfl,
    show 1+433%3 = 2 from rfl, show 664+2 = 666 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block73_entry0_1
#print axioms block73_entry0_1

theorem block73_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      35 34 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 667 432 = 11
  unfold entry
  simp only [show 4*(22+432/3) = 664 from rfl,
    show 1+432%3 = 1 from rfl, show 664+1 = 665 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block73_entry1_0
#print axioms block73_entry1_0

theorem block73_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      35 35 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 667 433 = 2147483640
  unfold entry
  simp only [show 4*(22+433/3) = 664 from rfl,
    show 1+433%3 = 2 from rfl, show 664+2 = 666 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block73_entry1_1
#print axioms block73_entry1_1

theorem block74_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      39 39 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 672 435 = 939524096
  unfold entry
  simp only [show 4*(22+435/3) = 668 from rfl,
    show 1+435%3 = 1 from rfl, show 668+1 = 669 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block74_entry0_0
#print axioms block74_entry0_0

theorem block75_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      37 37 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 684 444 = 1073741827
  unfold entry
  simp only [show 4*(22+444/3) = 680 from rfl,
    show 1+444%3 = 1 from rfl, show 680+1 = 681 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block75_entry0_0
#print axioms block75_entry0_0

theorem block75_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      37 38 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 684 445 = 1073741829
  unfold entry
  simp only [show 4*(22+445/3) = 680 from rfl,
    show 1+445%3 = 2 from rfl, show 680+2 = 682 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block75_entry0_1
#print axioms block75_entry0_1

theorem block75_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      38 37 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 683 444 = 11
  unfold entry
  simp only [show 4*(22+444/3) = 680 from rfl,
    show 1+444%3 = 1 from rfl, show 680+1 = 681 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block75_entry1_0
#print axioms block75_entry1_0

theorem block75_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      38 38 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 683 445 = 2147483640
  unfold entry
  simp only [show 4*(22+445/3) = 680 from rfl,
    show 1+445%3 = 2 from rfl, show 680+2 = 682 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block75_entry1_1
#print axioms block75_entry1_1

theorem block76_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      42 42 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 688 447 = 1879048192
  unfold entry
  simp only [show 4*(22+447/3) = 684 from rfl,
    show 1+447%3 = 1 from rfl, show 684+1 = 685 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block76_entry0_0
#print axioms block76_entry0_0

theorem block77_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      40 40 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 700 456 = 1073741827
  unfold entry
  simp only [show 4*(22+456/3) = 696 from rfl,
    show 1+456%3 = 1 from rfl, show 696+1 = 697 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block77_entry0_0
#print axioms block77_entry0_0

theorem block77_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      40 41 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 700 457 = 1073741829
  unfold entry
  simp only [show 4*(22+457/3) = 696 from rfl,
    show 1+457%3 = 2 from rfl, show 696+2 = 698 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block77_entry0_1
#print axioms block77_entry0_1

theorem block77_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      41 40 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 699 456 = 11
  unfold entry
  simp only [show 4*(22+456/3) = 696 from rfl,
    show 1+456%3 = 1 from rfl, show 696+1 = 697 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block77_entry1_0
#print axioms block77_entry1_0

theorem block77_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      41 41 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 699 457 = 2147483640
  unfold entry
  simp only [show 4*(22+457/3) = 696 from rfl,
    show 1+457%3 = 2 from rfl, show 696+2 = 698 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block77_entry1_1
#print axioms block77_entry1_1

end AspisV8R17.SourceMinor.DiagonalBlocks
