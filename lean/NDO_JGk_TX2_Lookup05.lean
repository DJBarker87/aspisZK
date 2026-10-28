import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup05
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (5,b) ∈ JGk_TX2_Group0_05.group) :
    JGk_TX2_Group0_00.stream.idxOf (5,b)=60+JGk_TX2_Group0_05.group.idxOf (5,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (5,b) ∈ JGk_TX2_Group2_05.group) :
    JGk_TX2_Group2_00.stream.idxOf (5,b)=60+JGk_TX2_Group2_05.group.idxOf (5,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (5,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (5,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 5) :
    JGk_TX2_SiblingBase.native0 5 b=JGf_TX2_M0Roots.siblingAt 5 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14304 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,14304)=0 from rfl]
    exact JGh_TX2_Siblings05.k0c060_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21280 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,21280)=1 from rfl]
    exact JGh_TX2_Siblings05.k0c061_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42112 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,42112)=2 from rfl]
    exact JGh_TX2_Siblings05.k0c062_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55392 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,55392)=3 from rfl]
    exact JGh_TX2_Siblings05.k0c063_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63808 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,63808)=4 from rfl]
    exact JGh_TX2_Siblings05.k0c064_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132384 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,132384)=5 from rfl]
    exact JGh_TX2_Siblings05.k0c065_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149568 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,149568)=6 from rfl]
    exact JGh_TX2_Siblings05.k0c066_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166176 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,166176)=7 from rfl]
    exact JGh_TX2_Siblings05.k0c067_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178048 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,178048)=8 from rfl]
    exact JGh_TX2_Siblings05.k0c068_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179584 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,179584)=9 from rfl]
    exact JGh_TX2_Siblings05.k0c069_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185600 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,185600)=10 from rfl]
    exact JGh_TX2_Siblings05.k0c070_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218048 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,218048)=11 from rfl]
    exact JGh_TX2_Siblings05.k0c071_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 5) :
    JGk_TX2_SiblingBase.native1 5 b=JGh_TX2_M1Roots.siblingAt 5 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14304 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,14304)=0 from rfl]
    exact JGh_TX2_Siblings05.k1c060_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21280 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,21280)=1 from rfl]
    exact JGh_TX2_Siblings05.k1c061_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42112 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,42112)=2 from rfl]
    exact JGh_TX2_Siblings05.k1c062_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55392 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,55392)=3 from rfl]
    exact JGh_TX2_Siblings05.k1c063_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63808 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,63808)=4 from rfl]
    exact JGh_TX2_Siblings05.k1c064_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132384 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,132384)=5 from rfl]
    exact JGh_TX2_Siblings05.k1c065_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149568 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,149568)=6 from rfl]
    exact JGh_TX2_Siblings05.k1c066_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166176 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,166176)=7 from rfl]
    exact JGh_TX2_Siblings05.k1c067_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178048 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,178048)=8 from rfl]
    exact JGh_TX2_Siblings05.k1c068_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179584 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,179584)=9 from rfl]
    exact JGh_TX2_Siblings05.k1c069_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185600 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,185600)=10 from rfl]
    exact JGh_TX2_Siblings05.k1c070_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218048 (by decide)]
    rw [show JGk_TX2_Group0_05.group.idxOf (5,218048)=11 from rfl]
    exact JGh_TX2_Siblings05.k1c071_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 5) :
    JGk_TX2_SiblingBase.native2 5 b=JGc_TX2_M2Roots.siblingAt 5 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3520 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,3520)=0 from rfl]
    exact JGh_TX2_Siblings05.k2c060_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5344 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,5344)=1 from rfl]
    exact JGh_TX2_Siblings05.k2c061_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10496 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,10496)=2 from rfl]
    exact JGh_TX2_Siblings05.k2c062_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13856 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,13856)=3 from rfl]
    exact JGh_TX2_Siblings05.k2c063_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15968 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,15968)=4 from rfl]
    exact JGh_TX2_Siblings05.k2c064_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33120 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,33120)=5 from rfl]
    exact JGh_TX2_Siblings05.k2c065_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37408 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,37408)=6 from rfl]
    exact JGh_TX2_Siblings05.k2c066_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41568 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,41568)=7 from rfl]
    exact JGh_TX2_Siblings05.k2c067_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44480 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,44480)=8 from rfl]
    exact JGh_TX2_Siblings05.k2c068_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44864 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,44864)=9 from rfl]
    exact JGh_TX2_Siblings05.k2c069_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46432 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,46432)=10 from rfl]
    exact JGh_TX2_Siblings05.k2c070_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54464 (by decide)]
    rw [show JGk_TX2_Group2_05.group.idxOf (5,54464)=11 from rfl]
    exact JGh_TX2_Siblings05.k2c071_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup05
