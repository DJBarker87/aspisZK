import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries07

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block78_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      45 45 = 469762048 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 704 459 = 469762048
  unfold entry
  simp only [show 4*(22+459/3) = 700 from rfl,
    show 1+459%3 = 1 from rfl, show 700+1 = 701 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block78_entry0_0
#print axioms block78_entry0_0

theorem block79_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      43 43 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 716 468 = 1073741827
  unfold entry
  simp only [show 4*(22+468/3) = 712 from rfl,
    show 1+468%3 = 1 from rfl, show 712+1 = 713 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block79_entry0_0
#print axioms block79_entry0_0

theorem block79_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      43 44 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 716 469 = 1073741829
  unfold entry
  simp only [show 4*(22+469/3) = 712 from rfl,
    show 1+469%3 = 2 from rfl, show 712+2 = 714 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block79_entry0_1
#print axioms block79_entry0_1

theorem block79_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      44 43 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 715 468 = 11
  unfold entry
  simp only [show 4*(22+468/3) = 712 from rfl,
    show 1+468%3 = 1 from rfl, show 712+1 = 713 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block79_entry1_0
#print axioms block79_entry1_0

theorem block79_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      44 44 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 715 469 = 2147483640
  unfold entry
  simp only [show 4*(22+469/3) = 712 from rfl,
    show 1+469%3 = 2 from rfl, show 712+2 = 714 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block79_entry1_1
#print axioms block79_entry1_1

theorem block80_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      48 48 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 720 471 = 1879048192
  unfold entry
  simp only [show 4*(22+471/3) = 716 from rfl,
    show 1+471%3 = 1 from rfl, show 716+1 = 717 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block80_entry0_0
#print axioms block80_entry0_0

theorem block81_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      46 46 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 732 480 = 1073741827
  unfold entry
  simp only [show 4*(22+480/3) = 728 from rfl,
    show 1+480%3 = 1 from rfl, show 728+1 = 729 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block81_entry0_0
#print axioms block81_entry0_0

theorem block81_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      46 47 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 732 481 = 1073741829
  unfold entry
  simp only [show 4*(22+481/3) = 728 from rfl,
    show 1+481%3 = 2 from rfl, show 728+2 = 730 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block81_entry0_1
#print axioms block81_entry0_1

theorem block81_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      47 46 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 731 480 = 11
  unfold entry
  simp only [show 4*(22+480/3) = 728 from rfl,
    show 1+480%3 = 1 from rfl, show 728+1 = 729 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block81_entry1_0
#print axioms block81_entry1_0

theorem block81_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      47 47 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 731 481 = 2147483640
  unfold entry
  simp only [show 4*(22+481/3) = 728 from rfl,
    show 1+481%3 = 2 from rfl, show 728+2 = 730 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block81_entry1_1
#print axioms block81_entry1_1

theorem block82_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      51 51 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 736 483 = 939524096
  unfold entry
  simp only [show 4*(22+483/3) = 732 from rfl,
    show 1+483%3 = 1 from rfl, show 732+1 = 733 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block82_entry0_0
#print axioms block82_entry0_0

theorem block83_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      49 49 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 748 492 = 1073741827
  unfold entry
  simp only [show 4*(22+492/3) = 744 from rfl,
    show 1+492%3 = 1 from rfl, show 744+1 = 745 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block83_entry0_0
#print axioms block83_entry0_0

theorem block83_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      49 50 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 748 493 = 1073741829
  unfold entry
  simp only [show 4*(22+493/3) = 744 from rfl,
    show 1+493%3 = 2 from rfl, show 744+2 = 746 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block83_entry0_1
#print axioms block83_entry0_1

theorem block83_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      50 49 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 747 492 = 11
  unfold entry
  simp only [show 4*(22+492/3) = 744 from rfl,
    show 1+492%3 = 1 from rfl, show 744+1 = 745 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block83_entry1_0
#print axioms block83_entry1_0

theorem block83_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      50 50 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 747 493 = 2147483640
  unfold entry
  simp only [show 4*(22+493/3) = 744 from rfl,
    show 1+493%3 = 2 from rfl, show 744+2 = 746 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block83_entry1_1
#print axioms block83_entry1_1

theorem block84_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      54 54 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 752 495 = 1879048192
  unfold entry
  simp only [show 4*(22+495/3) = 748 from rfl,
    show 1+495%3 = 1 from rfl, show 748+1 = 749 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block84_entry0_0
#print axioms block84_entry0_0

theorem block85_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      52 52 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 764 504 = 1073741827
  unfold entry
  simp only [show 4*(22+504/3) = 760 from rfl,
    show 1+504%3 = 1 from rfl, show 760+1 = 761 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block85_entry0_0
#print axioms block85_entry0_0

theorem block85_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      52 53 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 764 505 = 1073741829
  unfold entry
  simp only [show 4*(22+505/3) = 760 from rfl,
    show 1+505%3 = 2 from rfl, show 760+2 = 762 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block85_entry0_1
#print axioms block85_entry0_1

theorem block85_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      53 52 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 763 504 = 11
  unfold entry
  simp only [show 4*(22+504/3) = 760 from rfl,
    show 1+504%3 = 1 from rfl, show 760+1 = 761 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block85_entry1_0
#print axioms block85_entry1_0

theorem block85_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      53 53 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 763 505 = 2147483640
  unfold entry
  simp only [show 4*(22+505/3) = 760 from rfl,
    show 1+505%3 = 2 from rfl, show 760+2 = 762 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block85_entry1_1
#print axioms block85_entry1_1

theorem block86_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      57 57 = 117440512 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 768 507 = 117440512
  unfold entry
  simp only [show 4*(22+507/3) = 764 from rfl,
    show 1+507%3 = 1 from rfl, show 764+1 = 765 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block86_entry0_0
#print axioms block86_entry0_0

theorem block87_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      55 55 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 780 516 = 1073741827
  unfold entry
  simp only [show 4*(22+516/3) = 776 from rfl,
    show 1+516%3 = 1 from rfl, show 776+1 = 777 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block87_entry0_0
#print axioms block87_entry0_0

theorem block87_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      55 56 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 780 517 = 1073741829
  unfold entry
  simp only [show 4*(22+517/3) = 776 from rfl,
    show 1+517%3 = 2 from rfl, show 776+2 = 778 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block87_entry0_1
#print axioms block87_entry0_1

theorem block87_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      56 55 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 779 516 = 11
  unfold entry
  simp only [show 4*(22+516/3) = 776 from rfl,
    show 1+516%3 = 1 from rfl, show 776+1 = 777 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block87_entry1_0
#print axioms block87_entry1_0

theorem block87_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      56 56 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 779 517 = 2147483640
  unfold entry
  simp only [show 4*(22+517/3) = 776 from rfl,
    show 1+517%3 = 2 from rfl, show 776+2 = 778 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block87_entry1_1
#print axioms block87_entry1_1

theorem block88_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      60 60 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 784 519 = 1879048192
  unfold entry
  simp only [show 4*(22+519/3) = 780 from rfl,
    show 1+519%3 = 1 from rfl, show 780+1 = 781 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block88_entry0_0
#print axioms block88_entry0_0

theorem block89_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      58 58 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 796 528 = 1073741827
  unfold entry
  simp only [show 4*(22+528/3) = 792 from rfl,
    show 1+528%3 = 1 from rfl, show 792+1 = 793 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block89_entry0_0
#print axioms block89_entry0_0

theorem block89_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      58 59 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 796 529 = 1073741829
  unfold entry
  simp only [show 4*(22+529/3) = 792 from rfl,
    show 1+529%3 = 2 from rfl, show 792+2 = 794 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block89_entry0_1
#print axioms block89_entry0_1

theorem block89_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      59 58 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 795 528 = 11
  unfold entry
  simp only [show 4*(22+528/3) = 792 from rfl,
    show 1+528%3 = 1 from rfl, show 792+1 = 793 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block89_entry1_0
#print axioms block89_entry1_0

theorem block89_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      59 59 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 795 529 = 2147483640
  unfold entry
  simp only [show 4*(22+529/3) = 792 from rfl,
    show 1+529%3 = 2 from rfl, show 792+2 = 794 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block89_entry1_1
#print axioms block89_entry1_1

theorem block90_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      63 63 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 800 531 = 939524096
  unfold entry
  simp only [show 4*(22+531/3) = 796 from rfl,
    show 1+531%3 = 1 from rfl, show 796+1 = 797 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block90_entry0_0
#print axioms block90_entry0_0

theorem block91_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      61 61 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 812 540 = 1073741827
  unfold entry
  simp only [show 4*(22+540/3) = 808 from rfl,
    show 1+540%3 = 1 from rfl, show 808+1 = 809 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block91_entry0_0
#print axioms block91_entry0_0

end AspisV8R17.SourceMinor.DiagonalBlocks
