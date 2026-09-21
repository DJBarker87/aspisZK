import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries11

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block121_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      114 115 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 982 669 = 2147483625
  unfold entry
  simp only [show 4*(22+669/3) = 980 from rfl,
    show 1+669%3 = 1 from rfl, show 980+1 = 981 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block121_entry0_1
#print axioms block121_entry0_1

theorem block121_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      115 114 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 981 668 = 1073741829
  unfold entry
  simp only [show 4*(22+668/3) = 976 from rfl,
    show 1+668%3 = 3 from rfl, show 976+3 = 979 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block121_entry1_0
#print axioms block121_entry1_0

theorem block121_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      115 115 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 981 669 = 27
  unfold entry
  simp only [show 4*(22+669/3) = 980 from rfl,
    show 1+669%3 = 1 from rfl, show 980+1 = 981 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block121_entry1_1
#print axioms block121_entry1_1

theorem block122_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      116 116 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 986 671 = 1610612737
  unfold entry
  simp only [show 4*(22+671/3) = 980 from rfl,
    show 1+671%3 = 3 from rfl, show 980+3 = 983 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block122_entry0_0
#print axioms block122_entry0_0

theorem block122_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      116 117 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 986 672 = 2147483625
  unfold entry
  simp only [show 4*(22+672/3) = 984 from rfl,
    show 1+672%3 = 1 from rfl, show 984+1 = 985 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block122_entry0_1
#print axioms block122_entry0_1

theorem block122_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      117 116 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 985 671 = 1610612738
  unfold entry
  simp only [show 4*(22+671/3) = 980 from rfl,
    show 1+671%3 = 3 from rfl, show 980+3 = 983 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block122_entry1_0
#print axioms block122_entry1_0

theorem block122_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      117 117 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 985 672 = 27
  unfold entry
  simp only [show 4*(22+672/3) = 984 from rfl,
    show 1+672%3 = 1 from rfl, show 984+1 = 985 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block122_entry1_1
#print axioms block122_entry1_1

theorem block123_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      118 118 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 990 674 = 1073741827
  unfold entry
  simp only [show 4*(22+674/3) = 984 from rfl,
    show 1+674%3 = 3 from rfl, show 984+3 = 987 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block123_entry0_0
#print axioms block123_entry0_0

theorem block123_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      118 119 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 990 675 = 2147483625
  unfold entry
  simp only [show 4*(22+675/3) = 988 from rfl,
    show 1+675%3 = 1 from rfl, show 988+1 = 989 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block123_entry0_1
#print axioms block123_entry0_1

theorem block123_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      119 118 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 989 674 = 1073741829
  unfold entry
  simp only [show 4*(22+674/3) = 984 from rfl,
    show 1+674%3 = 3 from rfl, show 984+3 = 987 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block123_entry1_0
#print axioms block123_entry1_0

theorem block123_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      119 119 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 989 675 = 27
  unfold entry
  simp only [show 4*(22+675/3) = 988 from rfl,
    show 1+675%3 = 1 from rfl, show 988+1 = 989 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block123_entry1_1
#print axioms block123_entry1_1

theorem block124_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      120 120 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 994 677 = 939524096
  unfold entry
  simp only [show 4*(22+677/3) = 988 from rfl,
    show 1+677%3 = 3 from rfl, show 988+3 = 991 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block124_entry0_0
#print axioms block124_entry0_0

theorem block124_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      120 121 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 994 678 = 2147483625
  unfold entry
  simp only [show 4*(22+678/3) = 992 from rfl,
    show 1+678%3 = 1 from rfl, show 992+1 = 993 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block124_entry0_1
#print axioms block124_entry0_1

theorem block124_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      121 120 = 1476395008 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 993 677 = 1476395008
  unfold entry
  simp only [show 4*(22+677/3) = 988 from rfl,
    show 1+677%3 = 3 from rfl, show 988+3 = 991 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block124_entry1_0
#print axioms block124_entry1_0

theorem block124_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      121 121 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 993 678 = 27
  unfold entry
  simp only [show 4*(22+678/3) = 992 from rfl,
    show 1+678%3 = 1 from rfl, show 992+1 = 993 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block124_entry1_1
#print axioms block124_entry1_1

theorem block125_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      123 123 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 998 680 = 1073741827
  unfold entry
  simp only [show 4*(22+680/3) = 992 from rfl,
    show 1+680%3 = 3 from rfl, show 992+3 = 995 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block125_entry0_0
#print axioms block125_entry0_0

theorem block125_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      123 124 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 998 681 = 2147483625
  unfold entry
  simp only [show 4*(22+681/3) = 996 from rfl,
    show 1+681%3 = 1 from rfl, show 996+1 = 997 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block125_entry0_1
#print axioms block125_entry0_1

theorem block125_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      124 123 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 997 680 = 1073741829
  unfold entry
  simp only [show 4*(22+680/3) = 992 from rfl,
    show 1+680%3 = 3 from rfl, show 992+3 = 995 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block125_entry1_0
#print axioms block125_entry1_0

theorem block125_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      124 124 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 997 681 = 27
  unfold entry
  simp only [show 4*(22+681/3) = 996 from rfl,
    show 1+681%3 = 1 from rfl, show 996+1 = 997 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block125_entry1_1
#print axioms block125_entry1_1

theorem block126_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      125 125 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1002 683 = 1610612737
  unfold entry
  simp only [show 4*(22+683/3) = 996 from rfl,
    show 1+683%3 = 3 from rfl, show 996+3 = 999 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block126_entry0_0
#print axioms block126_entry0_0

theorem block126_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      125 126 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1002 684 = 2147483625
  unfold entry
  simp only [show 4*(22+684/3) = 1000 from rfl,
    show 1+684%3 = 1 from rfl, show 1000+1 = 1001 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block126_entry0_1
#print axioms block126_entry0_1

theorem block126_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      126 125 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1001 683 = 1610612738
  unfold entry
  simp only [show 4*(22+683/3) = 996 from rfl,
    show 1+683%3 = 3 from rfl, show 996+3 = 999 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block126_entry1_0
#print axioms block126_entry1_0

theorem block126_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      126 126 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1001 684 = 27
  unfold entry
  simp only [show 4*(22+684/3) = 1000 from rfl,
    show 1+684%3 = 1 from rfl, show 1000+1 = 1001 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block126_entry1_1
#print axioms block126_entry1_1

theorem block127_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      130 130 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1005 686 = 1073741829
  unfold entry
  simp only [show 4*(22+686/3) = 1000 from rfl,
    show 1+686%3 = 3 from rfl, show 1000+3 = 1003 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block127_entry0_0
#print axioms block127_entry0_0

theorem block127_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      130 131 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1005 687 = 27
  unfold entry
  simp only [show 4*(22+687/3) = 1004 from rfl,
    show 1+687%3 = 1 from rfl, show 1004+1 = 1005 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block127_entry0_1
#print axioms block127_entry0_1

theorem block127_entry0_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      130 132 = 28 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1005 688 = 28
  unfold entry
  simp only [show 4*(22+688/3) = 1004 from rfl,
    show 1+688%3 = 2 from rfl, show 1004+2 = 1006 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block127_entry0_2
#print axioms block127_entry0_2

theorem block127_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      131 130 = 0 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1008 686 = 0
  unfold entry
  simp only [show 4*(22+686/3) = 1000 from rfl,
    show 1+686%3 = 3 from rfl, show 1000+3 = 1003 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block127_entry1_0
#print axioms block127_entry1_0

theorem block127_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      131 131 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1008 687 = 1879048192
  unfold entry
  simp only [show 4*(22+687/3) = 1004 from rfl,
    show 1+687%3 = 1 from rfl, show 1004+1 = 1005 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block127_entry1_1
#print axioms block127_entry1_1

theorem block127_entry1_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      131 132 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1008 688 = 805306369
  unfold entry
  simp only [show 4*(22+688/3) = 1004 from rfl,
    show 1+688%3 = 2 from rfl, show 1004+2 = 1006 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block127_entry1_2
#print axioms block127_entry1_2

theorem block127_entry2_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      132 130 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1006 686 = 1073741827
  unfold entry
  simp only [show 4*(22+686/3) = 1000 from rfl,
    show 1+686%3 = 3 from rfl, show 1000+3 = 1003 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block127_entry2_0
#print axioms block127_entry2_0

theorem block127_entry2_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      132 131 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1006 687 = 2147483625
  unfold entry
  simp only [show 4*(22+687/3) = 1004 from rfl,
    show 1+687%3 = 1 from rfl, show 1004+1 = 1005 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block127_entry2_1
#print axioms block127_entry2_1

theorem block127_entry2_2 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      132 132 = 2147483616 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 1006 688 = 2147483616
  unfold entry
  simp only [show 4*(22+688/3) = 1004 from rfl,
    show 1+688%3 = 2 from rfl, show 1004+2 = 1006 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block127_entry2_2
#print axioms block127_entry2_2

end AspisV8R17.SourceMinor.DiagonalBlocks
