import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup08
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (8,b) ∈ JGk_TX2_Group0_08.group) :
    JGk_TX2_Group0_00.stream.idxOf (8,b)=96+JGk_TX2_Group0_08.group.idxOf (8,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (8,b) ∈ JGk_TX2_Group2_08.group) :
    JGk_TX2_Group2_00.stream.idxOf (8,b)=96+JGk_TX2_Group2_08.group.idxOf (8,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (8,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (8,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 8) :
    JGk_TX2_SiblingBase.native0 8 b=JGf_TX2_M0Roots.siblingAt 8 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 13824 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,13824)=0 from rfl]
    exact JGh_TX2_Siblings08.k0c096_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 20992 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,20992)=1 from rfl]
    exact JGh_TX2_Siblings08.k0c097_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42240 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,42240)=2 from rfl]
    exact JGh_TX2_Siblings08.k0c098_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55552 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,55552)=3 from rfl]
    exact JGh_TX2_Siblings08.k0c099_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63488 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,63488)=4 from rfl]
    exact JGh_TX2_Siblings08.k0c100_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132096 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,132096)=5 from rfl]
    exact JGh_TX2_Siblings08.k0c101_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149760 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,149760)=6 from rfl]
    exact JGh_TX2_Siblings08.k0c102_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 165888 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,165888)=7 from rfl]
    exact JGh_TX2_Siblings08.k0c103_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 177664 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,177664)=8 from rfl]
    exact JGh_TX2_Siblings08.k0c104_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179200 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,179200)=9 from rfl]
    exact JGh_TX2_Siblings08.k0c105_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185344 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,185344)=10 from rfl]
    exact JGh_TX2_Siblings08.k0c106_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 217600 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,217600)=11 from rfl]
    exact JGh_TX2_Siblings08.k0c107_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 8) :
    JGk_TX2_SiblingBase.native1 8 b=JGh_TX2_M1Roots.siblingAt 8 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 13824 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,13824)=0 from rfl]
    exact JGh_TX2_Siblings08.k1c096_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 20992 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,20992)=1 from rfl]
    exact JGh_TX2_Siblings08.k1c097_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42240 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,42240)=2 from rfl]
    exact JGh_TX2_Siblings08.k1c098_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55552 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,55552)=3 from rfl]
    exact JGh_TX2_Siblings08.k1c099_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63488 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,63488)=4 from rfl]
    exact JGh_TX2_Siblings08.k1c100_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132096 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,132096)=5 from rfl]
    exact JGh_TX2_Siblings08.k1c101_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149760 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,149760)=6 from rfl]
    exact JGh_TX2_Siblings08.k1c102_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 165888 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,165888)=7 from rfl]
    exact JGh_TX2_Siblings08.k1c103_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 177664 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,177664)=8 from rfl]
    exact JGh_TX2_Siblings08.k1c104_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179200 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,179200)=9 from rfl]
    exact JGh_TX2_Siblings08.k1c105_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185344 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,185344)=10 from rfl]
    exact JGh_TX2_Siblings08.k1c106_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 217600 (by decide)]
    rw [show JGk_TX2_Group0_08.group.idxOf (8,217600)=11 from rfl]
    exact JGh_TX2_Siblings08.k1c107_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 8) :
    JGk_TX2_SiblingBase.native2 8 b=JGc_TX2_M2Roots.siblingAt 8 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3072 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,3072)=0 from rfl]
    exact JGh_TX2_Siblings08.k2c096_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5376 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,5376)=1 from rfl]
    exact JGh_TX2_Siblings08.k2c097_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10240 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,10240)=2 from rfl]
    exact JGh_TX2_Siblings08.k2c098_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 14080 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,14080)=3 from rfl]
    exact JGh_TX2_Siblings08.k2c099_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 16128 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,16128)=4 from rfl]
    exact JGh_TX2_Siblings08.k2c100_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 32768 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,32768)=5 from rfl]
    exact JGh_TX2_Siblings08.k2c101_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37632 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,37632)=6 from rfl]
    exact JGh_TX2_Siblings08.k2c102_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41728 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,41728)=7 from rfl]
    exact JGh_TX2_Siblings08.k2c103_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44032 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,44032)=8 from rfl]
    exact JGh_TX2_Siblings08.k2c104_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44544 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,44544)=9 from rfl]
    exact JGh_TX2_Siblings08.k2c105_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46080 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,46080)=10 from rfl]
    exact JGh_TX2_Siblings08.k2c106_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54528 (by decide)]
    rw [show JGk_TX2_Group2_08.group.idxOf (8,54528)=11 from rfl]
    exact JGh_TX2_Siblings08.k2c107_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup08
