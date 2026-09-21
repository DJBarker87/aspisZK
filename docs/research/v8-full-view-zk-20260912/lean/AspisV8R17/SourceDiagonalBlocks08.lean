import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries08

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block91_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      61 62 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 812 541 = 1073741829
  unfold entry
  simp only [show 4*(22+541/3) = 808 from rfl,
    show 1+541%3 = 2 from rfl, show 808+2 = 810 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block91_entry0_1
#print axioms block91_entry0_1

theorem block91_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      62 61 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 811 540 = 11
  unfold entry
  simp only [show 4*(22+540/3) = 808 from rfl,
    show 1+540%3 = 1 from rfl, show 808+1 = 809 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block91_entry1_0
#print axioms block91_entry1_0

theorem block91_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      62 62 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 811 541 = 2147483640
  unfold entry
  simp only [show 4*(22+541/3) = 808 from rfl,
    show 1+541%3 = 2 from rfl, show 808+2 = 810 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block91_entry1_1
#print axioms block91_entry1_1

theorem block92_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      67 67 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 816 543 = 1879048192
  unfold entry
  simp only [show 4*(22+543/3) = 812 from rfl,
    show 1+543%3 = 1 from rfl, show 812+1 = 813 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block92_entry0_0
#print axioms block92_entry0_0

theorem block93_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      64 64 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 828 552 = 1073741827
  unfold entry
  simp only [show 4*(22+552/3) = 824 from rfl,
    show 1+552%3 = 1 from rfl, show 824+1 = 825 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block93_entry0_0
#print axioms block93_entry0_0

theorem block93_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      64 65 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 828 553 = 1073741829
  unfold entry
  simp only [show 4*(22+553/3) = 824 from rfl,
    show 1+553%3 = 2 from rfl, show 824+2 = 826 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block93_entry0_1
#print axioms block93_entry0_1

theorem block93_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      65 64 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 827 552 = 11
  unfold entry
  simp only [show 4*(22+552/3) = 824 from rfl,
    show 1+552%3 = 1 from rfl, show 824+1 = 825 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block93_entry1_0
#print axioms block93_entry1_0

theorem block93_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      65 65 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 827 553 = 2147483640
  unfold entry
  simp only [show 4*(22+553/3) = 824 from rfl,
    show 1+553%3 = 2 from rfl, show 824+2 = 826 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block93_entry1_1
#print axioms block93_entry1_1

theorem block94_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      72 72 = 469762048 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 832 555 = 469762048
  unfold entry
  simp only [show 4*(22+555/3) = 828 from rfl,
    show 1+555%3 = 1 from rfl, show 828+1 = 829 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block94_entry0_0
#print axioms block94_entry0_0

theorem block95_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      68 68 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 844 564 = 1073741827
  unfold entry
  simp only [show 4*(22+564/3) = 840 from rfl,
    show 1+564%3 = 1 from rfl, show 840+1 = 841 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block95_entry0_0
#print axioms block95_entry0_0

theorem block95_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      68 69 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 844 565 = 1073741829
  unfold entry
  simp only [show 4*(22+565/3) = 840 from rfl,
    show 1+565%3 = 2 from rfl, show 840+2 = 842 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block95_entry0_1
#print axioms block95_entry0_1

theorem block95_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      69 68 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 843 564 = 11
  unfold entry
  simp only [show 4*(22+564/3) = 840 from rfl,
    show 1+564%3 = 1 from rfl, show 840+1 = 841 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block95_entry1_0
#print axioms block95_entry1_0

theorem block95_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      69 69 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 843 565 = 2147483640
  unfold entry
  simp only [show 4*(22+565/3) = 840 from rfl,
    show 1+565%3 = 2 from rfl, show 840+2 = 842 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block95_entry1_1
#print axioms block95_entry1_1

theorem block96_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      73 73 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 848 567 = 1879048192
  unfold entry
  simp only [show 4*(22+567/3) = 844 from rfl,
    show 1+567%3 = 1 from rfl, show 844+1 = 845 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block96_entry0_0
#print axioms block96_entry0_0

theorem block97_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      74 74 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 860 576 = 1073741827
  unfold entry
  simp only [show 4*(22+576/3) = 856 from rfl,
    show 1+576%3 = 1 from rfl, show 856+1 = 857 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block97_entry0_0
#print axioms block97_entry0_0

theorem block98_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      79 79 = 939524096 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 864 579 = 939524096
  unfold entry
  simp only [show 4*(22+579/3) = 860 from rfl,
    show 1+579%3 = 1 from rfl, show 860+1 = 861 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block98_entry0_0
#print axioms block98_entry0_0

theorem block99_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      75 75 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 876 588 = 1073741827
  unfold entry
  simp only [show 4*(22+588/3) = 872 from rfl,
    show 1+588%3 = 1 from rfl, show 872+1 = 873 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block99_entry0_0
#print axioms block99_entry0_0

theorem block99_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      75 76 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 876 589 = 1073741829
  unfold entry
  simp only [show 4*(22+589/3) = 872 from rfl,
    show 1+589%3 = 2 from rfl, show 872+2 = 874 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block99_entry0_1
#print axioms block99_entry0_1

theorem block99_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      76 75 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 875 588 = 11
  unfold entry
  simp only [show 4*(22+588/3) = 872 from rfl,
    show 1+588%3 = 1 from rfl, show 872+1 = 873 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block99_entry1_0
#print axioms block99_entry1_0

theorem block99_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      76 76 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 875 589 = 2147483640
  unfold entry
  simp only [show 4*(22+589/3) = 872 from rfl,
    show 1+589%3 = 2 from rfl, show 872+2 = 874 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block99_entry1_1
#print axioms block99_entry1_1

theorem block100_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      82 82 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 880 591 = 1879048192
  unfold entry
  simp only [show 4*(22+591/3) = 876 from rfl,
    show 1+591%3 = 1 from rfl, show 876+1 = 877 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block100_entry0_0
#print axioms block100_entry0_0

theorem block101_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      80 80 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 892 600 = 1073741827
  unfold entry
  simp only [show 4*(22+600/3) = 888 from rfl,
    show 1+600%3 = 1 from rfl, show 888+1 = 889 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block101_entry0_0
#print axioms block101_entry0_0

theorem block101_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      80 81 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 892 601 = 1073741829
  unfold entry
  simp only [show 4*(22+601/3) = 888 from rfl,
    show 1+601%3 = 2 from rfl, show 888+2 = 890 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block101_entry0_1
#print axioms block101_entry0_1

theorem block101_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      81 80 = 11 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 891 600 = 11
  unfold entry
  simp only [show 4*(22+600/3) = 888 from rfl,
    show 1+600%3 = 1 from rfl, show 888+1 = 889 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block101_entry1_0
#print axioms block101_entry1_0

theorem block101_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      81 81 = 2147483640 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 891 601 = 2147483640
  unfold entry
  simp only [show 4*(22+601/3) = 888 from rfl,
    show 1+601%3 = 2 from rfl, show 888+2 = 890 from rfl]
  rw [show (2 : ZMod 2147483647)^2 = 4 from by decide]
  exact SourceBlocks.block101_entry1_1
#print axioms block101_entry1_1

theorem block102_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      85 85 = 234881024 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 896 603 = 234881024
  unfold entry
  simp only [show 4*(22+603/3) = 892 from rfl,
    show 1+603%3 = 1 from rfl, show 892+1 = 893 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block102_entry0_0
#print axioms block102_entry0_0

theorem block103_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      66 66 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 908 612 = 1073741827
  unfold entry
  simp only [show 4*(22+612/3) = 904 from rfl,
    show 1+612%3 = 1 from rfl, show 904+1 = 905 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block103_entry0_0
#print axioms block103_entry0_0

theorem block104_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      70 70 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 914 617 = 1879048192
  unfold entry
  simp only [show 4*(22+617/3) = 908 from rfl,
    show 1+617%3 = 3 from rfl, show 908+3 = 911 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block104_entry0_0
#print axioms block104_entry0_0

theorem block104_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      70 71 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 914 618 = 2147483625
  unfold entry
  simp only [show 4*(22+618/3) = 912 from rfl,
    show 1+618%3 = 1 from rfl, show 912+1 = 913 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block104_entry0_1
#print axioms block104_entry0_1

theorem block104_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      71 70 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 913 617 = 805306369
  unfold entry
  simp only [show 4*(22+617/3) = 908 from rfl,
    show 1+617%3 = 3 from rfl, show 908+3 = 911 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block104_entry1_0
#print axioms block104_entry1_0

theorem block104_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      71 71 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 913 618 = 27
  unfold entry
  simp only [show 4*(22+618/3) = 912 from rfl,
    show 1+618%3 = 1 from rfl, show 912+1 = 913 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block104_entry1_1
#print axioms block104_entry1_1

theorem block105_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      77 77 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 918 620 = 1073741827
  unfold entry
  simp only [show 4*(22+620/3) = 912 from rfl,
    show 1+620%3 = 3 from rfl, show 912+3 = 915 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block105_entry0_0
#print axioms block105_entry0_0

end AspisV8R17.SourceMinor.DiagonalBlocks
