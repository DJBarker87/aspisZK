import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup09
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (9,b) ∈ JGk_TX2_Group0_09.group) :
    JGk_TX2_Group0_00.stream.idxOf (9,b)=108+JGk_TX2_Group0_09.group.idxOf (9,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group0_08.group from by
    intro hm
    have e := JGk_TX2_Group0_08.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_09.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl,show JGk_TX2_Group0_08.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (9,b) ∈ JGk_TX2_Group2_09.group) :
    JGk_TX2_Group2_00.stream.idxOf (9,b)=108+JGk_TX2_Group2_09.group.idxOf (9,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_notMem (show (9,b) ∉ JGk_TX2_Group2_08.group from by
    intro hm
    have e := JGk_TX2_Group2_08.height (9,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_09.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl,show JGk_TX2_Group2_08.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 9) :
    JGk_TX2_SiblingBase.native0 9 b=JGf_TX2_M0Roots.siblingAt 9 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 13312 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,13312)=0 from rfl]
    exact JGh_TX2_Siblings09.k0c108_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 20480 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,20480)=1 from rfl]
    exact JGh_TX2_Siblings09.k0c109_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42496 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,42496)=2 from rfl]
    exact JGh_TX2_Siblings09.k0c110_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55808 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,55808)=3 from rfl]
    exact JGh_TX2_Siblings09.k0c111_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 64000 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,64000)=4 from rfl]
    exact JGh_TX2_Siblings09.k0c112_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132608 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,132608)=5 from rfl]
    exact JGh_TX2_Siblings09.k0c113_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 150016 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,150016)=6 from rfl]
    exact JGh_TX2_Siblings09.k0c114_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166400 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,166400)=7 from rfl]
    exact JGh_TX2_Siblings09.k0c115_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 177152 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,177152)=8 from rfl]
    exact JGh_TX2_Siblings09.k0c116_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179712 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,179712)=9 from rfl]
    exact JGh_TX2_Siblings09.k0c117_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185856 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,185856)=10 from rfl]
    exact JGh_TX2_Siblings09.k0c118_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 217088 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,217088)=11 from rfl]
    exact JGh_TX2_Siblings09.k0c119_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 9) :
    JGk_TX2_SiblingBase.native1 9 b=JGh_TX2_M1Roots.siblingAt 9 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 13312 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,13312)=0 from rfl]
    exact JGh_TX2_Siblings09.k1c108_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 20480 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,20480)=1 from rfl]
    exact JGh_TX2_Siblings09.k1c109_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42496 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,42496)=2 from rfl]
    exact JGh_TX2_Siblings09.k1c110_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55808 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,55808)=3 from rfl]
    exact JGh_TX2_Siblings09.k1c111_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 64000 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,64000)=4 from rfl]
    exact JGh_TX2_Siblings09.k1c112_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132608 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,132608)=5 from rfl]
    exact JGh_TX2_Siblings09.k1c113_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 150016 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,150016)=6 from rfl]
    exact JGh_TX2_Siblings09.k1c114_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166400 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,166400)=7 from rfl]
    exact JGh_TX2_Siblings09.k1c115_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 177152 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,177152)=8 from rfl]
    exact JGh_TX2_Siblings09.k1c116_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179712 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,179712)=9 from rfl]
    exact JGh_TX2_Siblings09.k1c117_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185856 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,185856)=10 from rfl]
    exact JGh_TX2_Siblings09.k1c118_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 217088 (by decide)]
    rw [show JGk_TX2_Group0_09.group.idxOf (9,217088)=11 from rfl]
    exact JGh_TX2_Siblings09.k1c119_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 9) :
    JGk_TX2_SiblingBase.native2 9 b=JGc_TX2_M2Roots.siblingAt 9 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3584 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,3584)=0 from rfl]
    exact JGh_TX2_Siblings09.k2c108_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5632 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,5632)=1 from rfl]
    exact JGh_TX2_Siblings09.k2c109_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10752 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,10752)=2 from rfl]
    exact JGh_TX2_Siblings09.k2c110_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13312 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,13312)=3 from rfl]
    exact JGh_TX2_Siblings09.k2c111_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15360 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,15360)=4 from rfl]
    exact JGh_TX2_Siblings09.k2c112_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33280 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,33280)=5 from rfl]
    exact JGh_TX2_Siblings09.k2c113_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 36864 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,36864)=6 from rfl]
    exact JGh_TX2_Siblings09.k2c114_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 40960 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,40960)=7 from rfl]
    exact JGh_TX2_Siblings09.k2c115_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46592 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,46592)=8 from rfl]
    exact JGh_TX2_Siblings09.k2c116_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54784 (by decide)]
    rw [show JGk_TX2_Group2_09.group.idxOf (9,54784)=9 from rfl]
    exact JGh_TX2_Siblings09.k2c117_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup09
