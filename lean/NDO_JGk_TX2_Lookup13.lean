import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup13
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (13,b) ∈ JGk_TX2_Group0_13.group) :
    JGk_TX2_Group0_00.stream.idxOf (13,b)=153+JGk_TX2_Group0_13.group.idxOf (13,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_08.group from by
    intro hm
    have e := JGk_TX2_Group0_08.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_09.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_09.group from by
    intro hm
    have e := JGk_TX2_Group0_09.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_10.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_10.group from by
    intro hm
    have e := JGk_TX2_Group0_10.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_11.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_11.group from by
    intro hm
    have e := JGk_TX2_Group0_11.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_12.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group0_12.group from by
    intro hm
    have e := JGk_TX2_Group0_12.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_13.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl,show JGk_TX2_Group0_08.group.length=12 from rfl,show JGk_TX2_Group0_09.group.length=12 from rfl,show JGk_TX2_Group0_10.group.length=12 from rfl,show JGk_TX2_Group0_11.group.length=10 from rfl,show JGk_TX2_Group0_12.group.length=11 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (13,b) ∈ JGk_TX2_Group2_13.group) :
    JGk_TX2_Group2_00.stream.idxOf (13,b)=137+JGk_TX2_Group2_13.group.idxOf (13,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_08.group from by
    intro hm
    have e := JGk_TX2_Group2_08.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_09.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_09.group from by
    intro hm
    have e := JGk_TX2_Group2_09.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_10.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_10.group from by
    intro hm
    have e := JGk_TX2_Group2_10.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_11.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_11.group from by
    intro hm
    have e := JGk_TX2_Group2_11.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_12.stream,List.idxOf_append_of_notMem (show (13,b) ∉ JGk_TX2_Group2_12.group from by
    intro hm
    have e := JGk_TX2_Group2_12.height (13,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_13.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl,show JGk_TX2_Group2_08.group.length=12 from rfl,show JGk_TX2_Group2_09.group.length=10 from rfl,show JGk_TX2_Group2_10.group.length=11 from rfl,show JGk_TX2_Group2_11.group.length=7 from rfl,show JGk_TX2_Group2_12.group.length=1 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 13) :
    JGk_TX2_SiblingBase.native0 13 b=JGf_TX2_M0Roots.siblingAt 13 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 0 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,0)=0 from rfl]
    exact JGh_TX2_Siblings13.k0c153_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 24576 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,24576)=1 from rfl]
    exact JGh_TX2_Siblings13.k0c154_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 32768 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,32768)=2 from rfl]
    exact JGh_TX2_Siblings13.k0c155_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 139264 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,139264)=3 from rfl]
    exact JGh_TX2_Siblings13.k0c156_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 155648 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,155648)=4 from rfl]
    exact JGh_TX2_Siblings13.k0c157_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 188416 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,188416)=5 from rfl]
    exact JGh_TX2_Siblings13.k0c158_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 221184 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,221184)=6 from rfl]
    exact JGh_TX2_Siblings13.k0c159_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 13) :
    JGk_TX2_SiblingBase.native1 13 b=JGh_TX2_M1Roots.siblingAt 13 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 0 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,0)=0 from rfl]
    exact JGh_TX2_Siblings13.k1c153_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 24576 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,24576)=1 from rfl]
    exact JGh_TX2_Siblings13.k1c154_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 32768 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,32768)=2 from rfl]
    exact JGh_TX2_Siblings13.k1c155_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 139264 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,139264)=3 from rfl]
    exact JGh_TX2_Siblings13.k1c156_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 155648 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,155648)=4 from rfl]
    exact JGh_TX2_Siblings13.k1c157_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 188416 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,188416)=5 from rfl]
    exact JGh_TX2_Siblings13.k1c158_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 221184 (by decide)]
    rw [show JGk_TX2_Group0_13.group.idxOf (13,221184)=6 from rfl]
    exact JGh_TX2_Siblings13.k1c159_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 13) :
    JGk_TX2_SiblingBase.native2 13 b=JGc_TX2_M2Roots.siblingAt 13 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 57344 (by decide)]
    rw [show JGk_TX2_Group2_13.group.idxOf (13,57344)=0 from rfl]
    exact JGh_TX2_Siblings13.k2c137_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup13
