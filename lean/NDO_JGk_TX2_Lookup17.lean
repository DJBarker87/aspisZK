import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup17
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset2 (b : Nat) (hb : (17,b) ∈ JGk_TX2_Group2_17.group) :
    JGk_TX2_Group2_00.stream.idxOf (17,b)=140+JGk_TX2_Group2_17.group.idxOf (17,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_08.group from by
    intro hm
    have e := JGk_TX2_Group2_08.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_09.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_09.group from by
    intro hm
    have e := JGk_TX2_Group2_09.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_10.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_10.group from by
    intro hm
    have e := JGk_TX2_Group2_10.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_11.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_11.group from by
    intro hm
    have e := JGk_TX2_Group2_11.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_12.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_12.group from by
    intro hm
    have e := JGk_TX2_Group2_12.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_13.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_13.group from by
    intro hm
    have e := JGk_TX2_Group2_13.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_14.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_14.group from by
    intro hm
    have e := JGk_TX2_Group2_14.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_15.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_15.group from by
    intro hm
    have e := JGk_TX2_Group2_15.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_16.stream,List.idxOf_append_of_notMem (show (17,b) ∉ JGk_TX2_Group2_16.group from by
    intro hm
    have e := JGk_TX2_Group2_16.height (17,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_17.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl,show JGk_TX2_Group2_08.group.length=12 from rfl,show JGk_TX2_Group2_09.group.length=10 from rfl,show JGk_TX2_Group2_10.group.length=11 from rfl,show JGk_TX2_Group2_11.group.length=7 from rfl,show JGk_TX2_Group2_12.group.length=1 from rfl,show JGk_TX2_Group2_13.group.length=1 from rfl,show JGk_TX2_Group2_14.group.length=1 from rfl,show JGk_TX2_Group2_15.group.length=0 from rfl,show JGk_TX2_Group2_16.group.length=1 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 17) :
    JGk_TX2_SiblingBase.native0 17 b=JGf_TX2_M0Roots.siblingAt 17 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  all_goals contradiction
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 17) :
    JGk_TX2_SiblingBase.native1 17 b=JGh_TX2_M1Roots.siblingAt 17 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  all_goals contradiction
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 17) :
    JGk_TX2_SiblingBase.native2 17 b=JGc_TX2_M2Roots.siblingAt 17 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 131072 (by decide)]
    rw [show JGk_TX2_Group2_17.group.idxOf (17,131072)=0 from rfl]
    exact JGh_TX2_Siblings17.k2c140_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup17
