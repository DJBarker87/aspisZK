import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup07
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (7,b) ∈ JGk_TX2_Group0_07.group) :
    JGk_TX2_Group0_00.stream.idxOf (7,b)=84+JGk_TX2_Group0_07.group.idxOf (7,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (7,b) ∈ JGk_TX2_Group2_07.group) :
    JGk_TX2_Group2_00.stream.idxOf (7,b)=84+JGk_TX2_Group2_07.group.idxOf (7,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (7,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (7,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 7) :
    JGk_TX2_SiblingBase.native0 7 b=JGf_TX2_M0Roots.siblingAt 7 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14080 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,14080)=0 from rfl]
    exact JGh_TX2_Siblings07.k0c084_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21376 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,21376)=1 from rfl]
    exact JGh_TX2_Siblings07.k0c085_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 41984 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,41984)=2 from rfl]
    exact JGh_TX2_Siblings07.k0c086_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55424 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,55424)=3 from rfl]
    exact JGh_TX2_Siblings07.k0c087_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63872 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,63872)=4 from rfl]
    exact JGh_TX2_Siblings07.k0c088_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132480 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,132480)=5 from rfl]
    exact JGh_TX2_Siblings07.k0c089_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149632 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,149632)=6 from rfl]
    exact JGh_TX2_Siblings07.k0c090_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166272 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,166272)=7 from rfl]
    exact JGh_TX2_Siblings07.k0c091_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 177920 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,177920)=8 from rfl]
    exact JGh_TX2_Siblings07.k0c092_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179456 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,179456)=9 from rfl]
    exact JGh_TX2_Siblings07.k0c093_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185728 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,185728)=10 from rfl]
    exact JGh_TX2_Siblings07.k0c094_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 217856 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,217856)=11 from rfl]
    exact JGh_TX2_Siblings07.k0c095_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 7) :
    JGk_TX2_SiblingBase.native1 7 b=JGh_TX2_M1Roots.siblingAt 7 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14080 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,14080)=0 from rfl]
    exact JGh_TX2_Siblings07.k1c084_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21376 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,21376)=1 from rfl]
    exact JGh_TX2_Siblings07.k1c085_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 41984 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,41984)=2 from rfl]
    exact JGh_TX2_Siblings07.k1c086_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55424 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,55424)=3 from rfl]
    exact JGh_TX2_Siblings07.k1c087_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63872 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,63872)=4 from rfl]
    exact JGh_TX2_Siblings07.k1c088_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132480 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,132480)=5 from rfl]
    exact JGh_TX2_Siblings07.k1c089_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149632 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,149632)=6 from rfl]
    exact JGh_TX2_Siblings07.k1c090_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166272 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,166272)=7 from rfl]
    exact JGh_TX2_Siblings07.k1c091_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 177920 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,177920)=8 from rfl]
    exact JGh_TX2_Siblings07.k1c092_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179456 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,179456)=9 from rfl]
    exact JGh_TX2_Siblings07.k1c093_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185728 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,185728)=10 from rfl]
    exact JGh_TX2_Siblings07.k1c094_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 217856 (by decide)]
    rw [show JGk_TX2_Group0_07.group.idxOf (7,217856)=11 from rfl]
    exact JGh_TX2_Siblings07.k1c095_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 7) :
    JGk_TX2_SiblingBase.native2 7 b=JGc_TX2_M2Roots.siblingAt 7 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3328 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,3328)=0 from rfl]
    exact JGh_TX2_Siblings07.k2c084_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5120 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,5120)=1 from rfl]
    exact JGh_TX2_Siblings07.k2c085_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10624 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,10624)=2 from rfl]
    exact JGh_TX2_Siblings07.k2c086_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13952 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,13952)=3 from rfl]
    exact JGh_TX2_Siblings07.k2c087_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 16000 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,16000)=4 from rfl]
    exact JGh_TX2_Siblings07.k2c088_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33152 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,33152)=5 from rfl]
    exact JGh_TX2_Siblings07.k2c089_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37504 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,37504)=6 from rfl]
    exact JGh_TX2_Siblings07.k2c090_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41600 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,41600)=7 from rfl]
    exact JGh_TX2_Siblings07.k2c091_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44288 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,44288)=8 from rfl]
    exact JGh_TX2_Siblings07.k2c092_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44928 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,44928)=9 from rfl]
    exact JGh_TX2_Siblings07.k2c093_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46464 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,46464)=10 from rfl]
    exact JGh_TX2_Siblings07.k2c094_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54272 (by decide)]
    rw [show JGk_TX2_Group2_07.group.idxOf (7,54272)=11 from rfl]
    exact JGh_TX2_Siblings07.k2c095_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup07
