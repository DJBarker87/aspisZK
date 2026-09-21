import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries10

/-! Generated source-matrix diagonal bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Preserve entry head before rewriting indices; never unfold full scatter. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.DiagonalBlocks
theorem block113_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      98 99 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 950 645 = 2147483625
  unfold entry
  simp only [show 4*(22+645/3) = 948 from rfl,
    show 1+645%3 = 1 from rfl, show 948+1 = 949 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block113_entry0_1
#print axioms block113_entry0_1

theorem block113_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      99 98 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 949 644 = 1073741829
  unfold entry
  simp only [show 4*(22+644/3) = 944 from rfl,
    show 1+644%3 = 3 from rfl, show 944+3 = 947 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block113_entry1_0
#print axioms block113_entry1_0

theorem block113_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      99 99 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 949 645 = 27
  unfold entry
  simp only [show 4*(22+645/3) = 948 from rfl,
    show 1+645%3 = 1 from rfl, show 948+1 = 949 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block113_entry1_1
#print axioms block113_entry1_1

theorem block114_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      100 100 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 954 647 = 1610612737
  unfold entry
  simp only [show 4*(22+647/3) = 948 from rfl,
    show 1+647%3 = 3 from rfl, show 948+3 = 951 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block114_entry0_0
#print axioms block114_entry0_0

theorem block114_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      100 101 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 954 648 = 2147483625
  unfold entry
  simp only [show 4*(22+648/3) = 952 from rfl,
    show 1+648%3 = 1 from rfl, show 952+1 = 953 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block114_entry0_1
#print axioms block114_entry0_1

theorem block114_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      101 100 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 953 647 = 1610612738
  unfold entry
  simp only [show 4*(22+647/3) = 948 from rfl,
    show 1+647%3 = 3 from rfl, show 948+3 = 951 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block114_entry1_0
#print axioms block114_entry1_0

theorem block114_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      101 101 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 953 648 = 27
  unfold entry
  simp only [show 4*(22+648/3) = 952 from rfl,
    show 1+648%3 = 1 from rfl, show 952+1 = 953 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block114_entry1_1
#print axioms block114_entry1_1

theorem block115_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      102 102 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 958 650 = 1073741827
  unfold entry
  simp only [show 4*(22+650/3) = 952 from rfl,
    show 1+650%3 = 3 from rfl, show 952+3 = 955 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block115_entry0_0
#print axioms block115_entry0_0

theorem block115_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      102 103 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 958 651 = 2147483625
  unfold entry
  simp only [show 4*(22+651/3) = 956 from rfl,
    show 1+651%3 = 1 from rfl, show 956+1 = 957 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block115_entry0_1
#print axioms block115_entry0_1

theorem block115_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      103 102 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 957 650 = 1073741829
  unfold entry
  simp only [show 4*(22+650/3) = 952 from rfl,
    show 1+650%3 = 3 from rfl, show 952+3 = 955 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block115_entry1_0
#print axioms block115_entry1_0

theorem block115_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      103 103 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 957 651 = 27
  unfold entry
  simp only [show 4*(22+651/3) = 956 from rfl,
    show 1+651%3 = 1 from rfl, show 956+1 = 957 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block115_entry1_1
#print axioms block115_entry1_1

theorem block116_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      104 104 = 469762048 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 962 653 = 469762048
  unfold entry
  simp only [show 4*(22+653/3) = 956 from rfl,
    show 1+653%3 = 3 from rfl, show 956+3 = 959 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block116_entry0_0
#print axioms block116_entry0_0

theorem block116_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      104 105 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 962 654 = 2147483625
  unfold entry
  simp only [show 4*(22+654/3) = 960 from rfl,
    show 1+654%3 = 1 from rfl, show 960+1 = 961 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block116_entry0_1
#print axioms block116_entry0_1

theorem block116_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      105 104 = 738197504 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 961 653 = 738197504
  unfold entry
  simp only [show 4*(22+653/3) = 956 from rfl,
    show 1+653%3 = 3 from rfl, show 956+3 = 959 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block116_entry1_0
#print axioms block116_entry1_0

theorem block116_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      105 105 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 961 654 = 27
  unfold entry
  simp only [show 4*(22+654/3) = 960 from rfl,
    show 1+654%3 = 1 from rfl, show 960+1 = 961 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block116_entry1_1
#print axioms block116_entry1_1

theorem block117_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      106 106 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 966 656 = 1073741827
  unfold entry
  simp only [show 4*(22+656/3) = 960 from rfl,
    show 1+656%3 = 3 from rfl, show 960+3 = 963 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block117_entry0_0
#print axioms block117_entry0_0

theorem block117_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      106 107 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 966 657 = 2147483625
  unfold entry
  simp only [show 4*(22+657/3) = 964 from rfl,
    show 1+657%3 = 1 from rfl, show 964+1 = 965 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block117_entry0_1
#print axioms block117_entry0_1

theorem block117_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      107 106 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 965 656 = 1073741829
  unfold entry
  simp only [show 4*(22+656/3) = 960 from rfl,
    show 1+656%3 = 3 from rfl, show 960+3 = 963 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block117_entry1_0
#print axioms block117_entry1_0

theorem block117_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      107 107 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 965 657 = 27
  unfold entry
  simp only [show 4*(22+657/3) = 964 from rfl,
    show 1+657%3 = 1 from rfl, show 964+1 = 965 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block117_entry1_1
#print axioms block117_entry1_1

theorem block118_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      108 108 = 1610612737 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 970 659 = 1610612737
  unfold entry
  simp only [show 4*(22+659/3) = 964 from rfl,
    show 1+659%3 = 3 from rfl, show 964+3 = 967 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block118_entry0_0
#print axioms block118_entry0_0

theorem block118_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      108 109 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 970 660 = 2147483625
  unfold entry
  simp only [show 4*(22+660/3) = 968 from rfl,
    show 1+660%3 = 1 from rfl, show 968+1 = 969 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block118_entry0_1
#print axioms block118_entry0_1

theorem block118_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      109 108 = 1610612738 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 969 659 = 1610612738
  unfold entry
  simp only [show 4*(22+659/3) = 964 from rfl,
    show 1+659%3 = 3 from rfl, show 964+3 = 967 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block118_entry1_0
#print axioms block118_entry1_0

theorem block118_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      109 109 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 969 660 = 27
  unfold entry
  simp only [show 4*(22+660/3) = 968 from rfl,
    show 1+660%3 = 1 from rfl, show 968+1 = 969 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block118_entry1_1
#print axioms block118_entry1_1

theorem block119_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      110 110 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 974 662 = 1073741827
  unfold entry
  simp only [show 4*(22+662/3) = 968 from rfl,
    show 1+662%3 = 3 from rfl, show 968+3 = 971 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block119_entry0_0
#print axioms block119_entry0_0

theorem block119_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      110 111 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 974 663 = 2147483625
  unfold entry
  simp only [show 4*(22+663/3) = 972 from rfl,
    show 1+663%3 = 1 from rfl, show 972+1 = 973 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block119_entry0_1
#print axioms block119_entry0_1

theorem block119_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      111 110 = 1073741829 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 973 662 = 1073741829
  unfold entry
  simp only [show 4*(22+662/3) = 968 from rfl,
    show 1+662%3 = 3 from rfl, show 968+3 = 971 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block119_entry1_0
#print axioms block119_entry1_0

theorem block119_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      111 111 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 973 663 = 27
  unfold entry
  simp only [show 4*(22+663/3) = 972 from rfl,
    show 1+663%3 = 1 from rfl, show 972+1 = 973 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block119_entry1_1
#print axioms block119_entry1_1

theorem block120_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      112 112 = 1879048192 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 978 665 = 1879048192
  unfold entry
  simp only [show 4*(22+665/3) = 972 from rfl,
    show 1+665%3 = 3 from rfl, show 972+3 = 975 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block120_entry0_0
#print axioms block120_entry0_0

theorem block120_entry0_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      112 113 = 2147483625 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 978 666 = 2147483625
  unfold entry
  simp only [show 4*(22+666/3) = 976 from rfl,
    show 1+666%3 = 1 from rfl, show 976+1 = 977 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block120_entry0_1
#print axioms block120_entry0_1

theorem block120_entry1_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      113 112 = 805306369 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 977 665 = 805306369
  unfold entry
  simp only [show 4*(22+665/3) = 972 from rfl,
    show 1+665%3 = 3 from rfl, show 972+3 = 975 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block120_entry1_0
#print axioms block120_entry1_0

theorem block120_entry1_1 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      113 113 = 27 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 977 666 = 27
  unfold entry
  simp only [show 4*(22+666/3) = 976 from rfl,
    show 1+666%3 = 1 from rfl, show 976+1 = 977 from rfl]
  rw [show (2 : ZMod 2147483647)^1 = 2 from by decide]
  exact SourceBlocks.block120_entry1_1
#print axioms block120_entry1_1

theorem block121_entry0_0 :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      114 114 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 982 668 = 1073741827
  unfold entry
  simp only [show 4*(22+668/3) = 976 from rfl,
    show 1+668%3 = 3 from rfl, show 976+3 = 979 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block121_entry0_0
#print axioms block121_entry0_0

end AspisV8R17.SourceMinor.DiagonalBlocks
