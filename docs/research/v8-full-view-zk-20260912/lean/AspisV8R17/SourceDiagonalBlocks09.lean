import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries09

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block105_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      77 78 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 918 621 = 2147483625
  unfold entry
  simp only [show 4*(22+621/3) = 916 from rfl,
    show 1+621%3 = 1 from rfl, show 916+1 = 917 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block105_entry0_1
#print axioms block105_entry0_1

theorem block105_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      78 77 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 917 620 = 1073741829
  unfold entry
  simp only [show 4*(22+620/3) = 912 from rfl,
    show 1+620%3 = 3 from rfl, show 912+3 = 915 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block105_entry1_0
#print axioms block105_entry1_0

theorem block105_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      78 78 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 917 621 = 27
  unfold entry
  simp only [show 4*(22+621/3) = 916 from rfl,
    show 1+621%3 = 1 from rfl, show 916+1 = 917 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block105_entry1_1
#print axioms block105_entry1_1

theorem block106_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      83 83 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 922 623 = 1610612737
  unfold entry
  simp only [show 4*(22+623/3) = 916 from rfl,
    show 1+623%3 = 3 from rfl, show 916+3 = 919 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block106_entry0_0
#print axioms block106_entry0_0

theorem block106_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      83 84 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 922 624 = 2147483625
  unfold entry
  simp only [show 4*(22+624/3) = 920 from rfl,
    show 1+624%3 = 1 from rfl, show 920+1 = 921 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block106_entry0_1
#print axioms block106_entry0_1

theorem block106_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      84 83 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 921 623 = 1610612738
  unfold entry
  simp only [show 4*(22+623/3) = 916 from rfl,
    show 1+623%3 = 3 from rfl, show 916+3 = 919 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block106_entry1_0
#print axioms block106_entry1_0

theorem block106_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      84 84 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 921 624 = 27
  unfold entry
  simp only [show 4*(22+624/3) = 920 from rfl,
    show 1+624%3 = 1 from rfl, show 920+1 = 921 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block106_entry1_1
#print axioms block106_entry1_1

theorem block107_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      86 86 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 926 626 = 1073741827
  unfold entry
  simp only [show 4*(22+626/3) = 920 from rfl,
    show 1+626%3 = 3 from rfl, show 920+3 = 923 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block107_entry0_0
#print axioms block107_entry0_0

theorem block107_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      86 87 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 926 627 = 2147483625
  unfold entry
  simp only [show 4*(22+627/3) = 924 from rfl,
    show 1+627%3 = 1 from rfl, show 924+1 = 925 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block107_entry0_1
#print axioms block107_entry0_1

theorem block107_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      87 86 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 925 626 = 1073741829
  unfold entry
  simp only [show 4*(22+626/3) = 920 from rfl,
    show 1+626%3 = 3 from rfl, show 920+3 = 923 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block107_entry1_0
#print axioms block107_entry1_0

theorem block107_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      87 87 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 925 627 = 27
  unfold entry
  simp only [show 4*(22+627/3) = 924 from rfl,
    show 1+627%3 = 1 from rfl, show 924+1 = 925 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block107_entry1_1
#print axioms block107_entry1_1

theorem block108_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      88 88 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 930 629 = 939524096
  unfold entry
  simp only [show 4*(22+629/3) = 924 from rfl,
    show 1+629%3 = 3 from rfl, show 924+3 = 927 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block108_entry0_0
#print axioms block108_entry0_0

theorem block108_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      88 89 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 930 630 = 2147483625
  unfold entry
  simp only [show 4*(22+630/3) = 928 from rfl,
    show 1+630%3 = 1 from rfl, show 928+1 = 929 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block108_entry0_1
#print axioms block108_entry0_1

theorem block108_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      89 88 = 1476395008 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 929 629 = 1476395008
  unfold entry
  simp only [show 4*(22+629/3) = 924 from rfl,
    show 1+629%3 = 3 from rfl, show 924+3 = 927 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block108_entry1_0
#print axioms block108_entry1_0

theorem block108_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      89 89 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 929 630 = 27
  unfold entry
  simp only [show 4*(22+630/3) = 928 from rfl,
    show 1+630%3 = 1 from rfl, show 928+1 = 929 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block108_entry1_1
#print axioms block108_entry1_1

theorem block109_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      90 90 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 934 632 = 1073741827
  unfold entry
  simp only [show 4*(22+632/3) = 928 from rfl,
    show 1+632%3 = 3 from rfl, show 928+3 = 931 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block109_entry0_0
#print axioms block109_entry0_0

theorem block109_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      90 91 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 934 633 = 2147483625
  unfold entry
  simp only [show 4*(22+633/3) = 932 from rfl,
    show 1+633%3 = 1 from rfl, show 932+1 = 933 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block109_entry0_1
#print axioms block109_entry0_1

theorem block109_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      91 90 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 933 632 = 1073741829
  unfold entry
  simp only [show 4*(22+632/3) = 928 from rfl,
    show 1+632%3 = 3 from rfl, show 928+3 = 931 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block109_entry1_0
#print axioms block109_entry1_0

theorem block109_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      91 91 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 933 633 = 27
  unfold entry
  simp only [show 4*(22+633/3) = 932 from rfl,
    show 1+633%3 = 1 from rfl, show 932+1 = 933 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block109_entry1_1
#print axioms block109_entry1_1

theorem block110_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      92 92 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 938 635 = 1610612737
  unfold entry
  simp only [show 4*(22+635/3) = 932 from rfl,
    show 1+635%3 = 3 from rfl, show 932+3 = 935 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block110_entry0_0
#print axioms block110_entry0_0

theorem block110_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      92 93 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 938 636 = 2147483625
  unfold entry
  simp only [show 4*(22+636/3) = 936 from rfl,
    show 1+636%3 = 1 from rfl, show 936+1 = 937 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block110_entry0_1
#print axioms block110_entry0_1

theorem block110_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      93 92 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 937 635 = 1610612738
  unfold entry
  simp only [show 4*(22+635/3) = 932 from rfl,
    show 1+635%3 = 3 from rfl, show 932+3 = 935 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block110_entry1_0
#print axioms block110_entry1_0

theorem block110_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      93 93 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 937 636 = 27
  unfold entry
  simp only [show 4*(22+636/3) = 936 from rfl,
    show 1+636%3 = 1 from rfl, show 936+1 = 937 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block110_entry1_1
#print axioms block110_entry1_1

theorem block111_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      94 94 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 942 638 = 1073741827
  unfold entry
  simp only [show 4*(22+638/3) = 936 from rfl,
    show 1+638%3 = 3 from rfl, show 936+3 = 939 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block111_entry0_0
#print axioms block111_entry0_0

theorem block111_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      94 95 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 942 639 = 2147483625
  unfold entry
  simp only [show 4*(22+639/3) = 940 from rfl,
    show 1+639%3 = 1 from rfl, show 940+1 = 941 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block111_entry0_1
#print axioms block111_entry0_1

theorem block111_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      95 94 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 941 638 = 1073741829
  unfold entry
  simp only [show 4*(22+638/3) = 936 from rfl,
    show 1+638%3 = 3 from rfl, show 936+3 = 939 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block111_entry1_0
#print axioms block111_entry1_0

theorem block111_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      95 95 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 941 639 = 27
  unfold entry
  simp only [show 4*(22+639/3) = 940 from rfl,
    show 1+639%3 = 1 from rfl, show 940+1 = 941 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block111_entry1_1
#print axioms block111_entry1_1

theorem block112_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      96 96 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 946 641 = 1879048192
  unfold entry
  simp only [show 4*(22+641/3) = 940 from rfl,
    show 1+641%3 = 3 from rfl, show 940+3 = 943 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block112_entry0_0
#print axioms block112_entry0_0

theorem block112_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      96 97 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 946 642 = 2147483625
  unfold entry
  simp only [show 4*(22+642/3) = 944 from rfl,
    show 1+642%3 = 1 from rfl, show 944+1 = 945 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block112_entry0_1
#print axioms block112_entry0_1

theorem block112_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      97 96 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 945 641 = 805306369
  unfold entry
  simp only [show 4*(22+641/3) = 940 from rfl,
    show 1+641%3 = 3 from rfl, show 940+3 = 943 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block112_entry1_0
#print axioms block112_entry1_0

theorem block112_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      97 97 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 945 642 = 27
  unfold entry
  simp only [show 4*(22+642/3) = 944 from rfl,
    show 1+642%3 = 1 from rfl, show 944+1 = 945 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block112_entry1_1
#print axioms block112_entry1_1

theorem block113_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      98 98 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 950 644 = 1073741827
  unfold entry
  simp only [show 4*(22+644/3) = 944 from rfl,
    show 1+644%3 = 3 from rfl, show 944+3 = 947 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block113_entry0_0
#print axioms block113_entry0_0

end AspisV8R17.SourceMinor.DiagonalBlocks
