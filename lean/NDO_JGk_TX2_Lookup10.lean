import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup10
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (10,b) ∈ JGk_TX2_Group0_10.group) :
    JGk_TX2_Group0_00.stream.idxOf (10,b)=120+JGk_TX2_Group0_10.group.idxOf (10,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_08.group from by
    intro hm
    have e := JGk_TX2_Group0_08.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_09.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group0_09.group from by
    intro hm
    have e := JGk_TX2_Group0_09.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_10.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl,show JGk_TX2_Group0_08.group.length=12 from rfl,show JGk_TX2_Group0_09.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (10,b) ∈ JGk_TX2_Group2_10.group) :
    JGk_TX2_Group2_00.stream.idxOf (10,b)=118+JGk_TX2_Group2_10.group.idxOf (10,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_08.group from by
    intro hm
    have e := JGk_TX2_Group2_08.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_09.stream,List.idxOf_append_of_notMem (show (10,b) ∉ JGk_TX2_Group2_09.group from by
    intro hm
    have e := JGk_TX2_Group2_09.height (10,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_10.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl,show JGk_TX2_Group2_08.group.length=12 from rfl,show JGk_TX2_Group2_09.group.length=10 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 10) :
    JGk_TX2_SiblingBase.native0 10 b=JGf_TX2_M0Roots.siblingAt 10 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 12288 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,12288)=0 from rfl]
    exact JGh_TX2_Siblings10.k0c120_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21504 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,21504)=1 from rfl]
    exact JGh_TX2_Siblings10.k0c121_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 40960 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,40960)=2 from rfl]
    exact JGh_TX2_Siblings10.k0c122_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 56320 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,56320)=3 from rfl]
    exact JGh_TX2_Siblings10.k0c123_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 64512 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,64512)=4 from rfl]
    exact JGh_TX2_Siblings10.k0c124_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 131072 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,131072)=5 from rfl]
    exact JGh_TX2_Siblings10.k0c125_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 150528 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,150528)=6 from rfl]
    exact JGh_TX2_Siblings10.k0c126_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166912 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,166912)=7 from rfl]
    exact JGh_TX2_Siblings10.k0c127_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 176128 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,176128)=8 from rfl]
    exact JGh_TX2_Siblings10.k0c128_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178176 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,178176)=9 from rfl]
    exact JGh_TX2_Siblings10.k0c129_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 184320 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,184320)=10 from rfl]
    exact JGh_TX2_Siblings10.k0c130_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218112 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,218112)=11 from rfl]
    exact JGh_TX2_Siblings10.k0c131_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 10) :
    JGk_TX2_SiblingBase.native1 10 b=JGh_TX2_M1Roots.siblingAt 10 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 12288 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,12288)=0 from rfl]
    exact JGh_TX2_Siblings10.k1c120_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21504 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,21504)=1 from rfl]
    exact JGh_TX2_Siblings10.k1c121_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 40960 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,40960)=2 from rfl]
    exact JGh_TX2_Siblings10.k1c122_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 56320 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,56320)=3 from rfl]
    exact JGh_TX2_Siblings10.k1c123_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 64512 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,64512)=4 from rfl]
    exact JGh_TX2_Siblings10.k1c124_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 131072 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,131072)=5 from rfl]
    exact JGh_TX2_Siblings10.k1c125_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 150528 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,150528)=6 from rfl]
    exact JGh_TX2_Siblings10.k1c126_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166912 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,166912)=7 from rfl]
    exact JGh_TX2_Siblings10.k1c127_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 176128 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,176128)=8 from rfl]
    exact JGh_TX2_Siblings10.k1c128_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178176 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,178176)=9 from rfl]
    exact JGh_TX2_Siblings10.k1c129_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 184320 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,184320)=10 from rfl]
    exact JGh_TX2_Siblings10.k1c130_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218112 (by decide)]
    rw [show JGk_TX2_Group0_10.group.idxOf (10,218112)=11 from rfl]
    exact JGh_TX2_Siblings10.k1c131_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 10) :
    JGk_TX2_SiblingBase.native2 10 b=JGc_TX2_M2Roots.siblingAt 10 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 2048 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,2048)=0 from rfl]
    exact JGh_TX2_Siblings10.k2c118_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 4096 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,4096)=1 from rfl]
    exact JGh_TX2_Siblings10.k2c119_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 11264 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,11264)=2 from rfl]
    exact JGh_TX2_Siblings10.k2c120_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 12288 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,12288)=3 from rfl]
    exact JGh_TX2_Siblings10.k2c121_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 14336 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,14336)=4 from rfl]
    exact JGh_TX2_Siblings10.k2c122_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33792 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,33792)=5 from rfl]
    exact JGh_TX2_Siblings10.k2c123_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37888 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,37888)=6 from rfl]
    exact JGh_TX2_Siblings10.k2c124_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41984 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,41984)=7 from rfl]
    exact JGh_TX2_Siblings10.k2c125_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 43008 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,43008)=8 from rfl]
    exact JGh_TX2_Siblings10.k2c126_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 45056 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,45056)=9 from rfl]
    exact JGh_TX2_Siblings10.k2c127_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 53248 (by decide)]
    rw [show JGk_TX2_Group2_10.group.idxOf (10,53248)=10 from rfl]
    exact JGh_TX2_Siblings10.k2c128_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup10
