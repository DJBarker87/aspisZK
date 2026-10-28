import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup06
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (6,b) ∈ JGk_TX2_Group0_06.group) :
    JGk_TX2_Group0_00.stream.idxOf (6,b)=72+JGk_TX2_Group0_06.group.idxOf (6,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (6,b) ∈ JGk_TX2_Group2_06.group) :
    JGk_TX2_Group2_00.stream.idxOf (6,b)=72+JGk_TX2_Group2_06.group.idxOf (6,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (6,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (6,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 6) :
    JGk_TX2_SiblingBase.native0 6 b=JGf_TX2_M0Roots.siblingAt 6 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14208 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,14208)=0 from rfl]
    exact JGh_TX2_Siblings06.k0c072_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21312 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,21312)=1 from rfl]
    exact JGh_TX2_Siblings06.k0c073_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42176 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,42176)=2 from rfl]
    exact JGh_TX2_Siblings06.k0c074_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55296 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,55296)=3 from rfl]
    exact JGh_TX2_Siblings06.k0c075_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63744 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,63744)=4 from rfl]
    exact JGh_TX2_Siblings06.k0c076_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132416 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,132416)=5 from rfl]
    exact JGh_TX2_Siblings06.k0c077_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149504 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,149504)=6 from rfl]
    exact JGh_TX2_Siblings06.k0c078_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166208 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,166208)=7 from rfl]
    exact JGh_TX2_Siblings06.k0c079_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178112 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,178112)=8 from rfl]
    exact JGh_TX2_Siblings06.k0c080_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179648 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,179648)=9 from rfl]
    exact JGh_TX2_Siblings06.k0c081_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185664 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,185664)=10 from rfl]
    exact JGh_TX2_Siblings06.k0c082_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 217984 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,217984)=11 from rfl]
    exact JGh_TX2_Siblings06.k0c083_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 6) :
    JGk_TX2_SiblingBase.native1 6 b=JGh_TX2_M1Roots.siblingAt 6 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14208 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,14208)=0 from rfl]
    exact JGh_TX2_Siblings06.k1c072_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21312 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,21312)=1 from rfl]
    exact JGh_TX2_Siblings06.k1c073_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42176 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,42176)=2 from rfl]
    exact JGh_TX2_Siblings06.k1c074_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55296 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,55296)=3 from rfl]
    exact JGh_TX2_Siblings06.k1c075_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63744 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,63744)=4 from rfl]
    exact JGh_TX2_Siblings06.k1c076_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132416 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,132416)=5 from rfl]
    exact JGh_TX2_Siblings06.k1c077_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149504 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,149504)=6 from rfl]
    exact JGh_TX2_Siblings06.k1c078_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166208 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,166208)=7 from rfl]
    exact JGh_TX2_Siblings06.k1c079_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178112 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,178112)=8 from rfl]
    exact JGh_TX2_Siblings06.k1c080_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179648 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,179648)=9 from rfl]
    exact JGh_TX2_Siblings06.k1c081_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185664 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,185664)=10 from rfl]
    exact JGh_TX2_Siblings06.k1c082_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 217984 (by decide)]
    rw [show JGk_TX2_Group0_06.group.idxOf (6,217984)=11 from rfl]
    exact JGh_TX2_Siblings06.k1c083_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 6) :
    JGk_TX2_SiblingBase.native2 6 b=JGc_TX2_M2Roots.siblingAt 6 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3456 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,3456)=0 from rfl]
    exact JGh_TX2_Siblings06.k2c072_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5248 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,5248)=1 from rfl]
    exact JGh_TX2_Siblings06.k2c073_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10560 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,10560)=2 from rfl]
    exact JGh_TX2_Siblings06.k2c074_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13888 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,13888)=3 from rfl]
    exact JGh_TX2_Siblings06.k2c075_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15872 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,15872)=4 from rfl]
    exact JGh_TX2_Siblings06.k2c076_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33024 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,33024)=5 from rfl]
    exact JGh_TX2_Siblings06.k2c077_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37440 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,37440)=6 from rfl]
    exact JGh_TX2_Siblings06.k2c078_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41472 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,41472)=7 from rfl]
    exact JGh_TX2_Siblings06.k2c079_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44416 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,44416)=8 from rfl]
    exact JGh_TX2_Siblings06.k2c080_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44800 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,44800)=9 from rfl]
    exact JGh_TX2_Siblings06.k2c081_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46336 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,46336)=10 from rfl]
    exact JGh_TX2_Siblings06.k2c082_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54400 (by decide)]
    rw [show JGk_TX2_Group2_06.group.idxOf (6,54400)=11 from rfl]
    exact JGh_TX2_Siblings06.k2c083_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup06
