import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup15
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (15,b) ∈ JGk_TX2_Group0_15.group) :
    JGk_TX2_Group0_00.stream.idxOf (15,b)=161+JGk_TX2_Group0_15.group.idxOf (15,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_08.group from by
    intro hm
    have e := JGk_TX2_Group0_08.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_09.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_09.group from by
    intro hm
    have e := JGk_TX2_Group0_09.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_10.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_10.group from by
    intro hm
    have e := JGk_TX2_Group0_10.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_11.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_11.group from by
    intro hm
    have e := JGk_TX2_Group0_11.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_12.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_12.group from by
    intro hm
    have e := JGk_TX2_Group0_12.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_13.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_13.group from by
    intro hm
    have e := JGk_TX2_Group0_13.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_14.stream,List.idxOf_append_of_notMem (show (15,b) ∉ JGk_TX2_Group0_14.group from by
    intro hm
    have e := JGk_TX2_Group0_14.height (15,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_15.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl,show JGk_TX2_Group0_08.group.length=12 from rfl,show JGk_TX2_Group0_09.group.length=12 from rfl,show JGk_TX2_Group0_10.group.length=12 from rfl,show JGk_TX2_Group0_11.group.length=10 from rfl,show JGk_TX2_Group0_12.group.length=11 from rfl,show JGk_TX2_Group0_13.group.length=7 from rfl,show JGk_TX2_Group0_14.group.length=1 from rfl]
  all_goals omega
#print axioms offset0
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 15) :
    JGk_TX2_SiblingBase.native0 15 b=JGf_TX2_M0Roots.siblingAt 15 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 229376 (by decide)]
    rw [show JGk_TX2_Group0_15.group.idxOf (15,229376)=0 from rfl]
    exact JGh_TX2_Siblings15.k0c161_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 15) :
    JGk_TX2_SiblingBase.native1 15 b=JGh_TX2_M1Roots.siblingAt 15 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 229376 (by decide)]
    rw [show JGk_TX2_Group0_15.group.idxOf (15,229376)=0 from rfl]
    exact JGh_TX2_Siblings15.k1c161_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 15) :
    JGk_TX2_SiblingBase.native2 15 b=JGc_TX2_M2Roots.siblingAt 15 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  all_goals contradiction
#print axioms source2
end AspisR1.JGk_TX2_Lookup15
