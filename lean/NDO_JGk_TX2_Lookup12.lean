import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup12
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (12,b) ∈ JGk_TX2_Group0_12.group) :
    JGk_TX2_Group0_00.stream.idxOf (12,b)=142+JGk_TX2_Group0_12.group.idxOf (12,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_08.group from by
    intro hm
    have e := JGk_TX2_Group0_08.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_09.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_09.group from by
    intro hm
    have e := JGk_TX2_Group0_09.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_10.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_10.group from by
    intro hm
    have e := JGk_TX2_Group0_10.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_11.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group0_11.group from by
    intro hm
    have e := JGk_TX2_Group0_11.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_12.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl,show JGk_TX2_Group0_08.group.length=12 from rfl,show JGk_TX2_Group0_09.group.length=12 from rfl,show JGk_TX2_Group0_10.group.length=12 from rfl,show JGk_TX2_Group0_11.group.length=10 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (12,b) ∈ JGk_TX2_Group2_12.group) :
    JGk_TX2_Group2_00.stream.idxOf (12,b)=136+JGk_TX2_Group2_12.group.idxOf (12,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_08.group from by
    intro hm
    have e := JGk_TX2_Group2_08.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_09.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_09.group from by
    intro hm
    have e := JGk_TX2_Group2_09.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_10.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_10.group from by
    intro hm
    have e := JGk_TX2_Group2_10.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_11.stream,List.idxOf_append_of_notMem (show (12,b) ∉ JGk_TX2_Group2_11.group from by
    intro hm
    have e := JGk_TX2_Group2_11.height (12,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_12.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl,show JGk_TX2_Group2_08.group.length=12 from rfl,show JGk_TX2_Group2_09.group.length=10 from rfl,show JGk_TX2_Group2_10.group.length=11 from rfl,show JGk_TX2_Group2_11.group.length=7 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 12) :
    JGk_TX2_SiblingBase.native0 12 b=JGf_TX2_M0Roots.siblingAt 12 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 8192 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,8192)=0 from rfl]
    exact JGh_TX2_Siblings12.k0c142_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 16384 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,16384)=1 from rfl]
    exact JGh_TX2_Siblings12.k0c143_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 45056 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,45056)=2 from rfl]
    exact JGh_TX2_Siblings12.k0c144_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 49152 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,49152)=3 from rfl]
    exact JGh_TX2_Siblings12.k0c145_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 57344 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,57344)=4 from rfl]
    exact JGh_TX2_Siblings12.k0c146_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 135168 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,135168)=5 from rfl]
    exact JGh_TX2_Siblings12.k0c147_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 151552 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,151552)=6 from rfl]
    exact JGh_TX2_Siblings12.k0c148_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 167936 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,167936)=7 from rfl]
    exact JGh_TX2_Siblings12.k0c149_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 172032 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,172032)=8 from rfl]
    exact JGh_TX2_Siblings12.k0c150_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 180224 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,180224)=9 from rfl]
    exact JGh_TX2_Siblings12.k0c151_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 212992 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,212992)=10 from rfl]
    exact JGh_TX2_Siblings12.k0c152_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 12) :
    JGk_TX2_SiblingBase.native1 12 b=JGh_TX2_M1Roots.siblingAt 12 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 8192 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,8192)=0 from rfl]
    exact JGh_TX2_Siblings12.k1c142_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 16384 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,16384)=1 from rfl]
    exact JGh_TX2_Siblings12.k1c143_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 45056 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,45056)=2 from rfl]
    exact JGh_TX2_Siblings12.k1c144_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 49152 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,49152)=3 from rfl]
    exact JGh_TX2_Siblings12.k1c145_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 57344 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,57344)=4 from rfl]
    exact JGh_TX2_Siblings12.k1c146_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 135168 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,135168)=5 from rfl]
    exact JGh_TX2_Siblings12.k1c147_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 151552 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,151552)=6 from rfl]
    exact JGh_TX2_Siblings12.k1c148_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 167936 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,167936)=7 from rfl]
    exact JGh_TX2_Siblings12.k1c149_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 172032 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,172032)=8 from rfl]
    exact JGh_TX2_Siblings12.k1c150_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 180224 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,180224)=9 from rfl]
    exact JGh_TX2_Siblings12.k1c151_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 212992 (by decide)]
    rw [show JGk_TX2_Group0_12.group.idxOf (12,212992)=10 from rfl]
    exact JGh_TX2_Siblings12.k1c152_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 12) :
    JGk_TX2_SiblingBase.native2 12 b=JGc_TX2_M2Roots.siblingAt 12 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 49152 (by decide)]
    rw [show JGk_TX2_Group2_12.group.idxOf (12,49152)=0 from rfl]
    exact JGh_TX2_Siblings12.k2c136_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup12
