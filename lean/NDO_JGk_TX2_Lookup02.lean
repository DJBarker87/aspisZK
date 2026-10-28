import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup02
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (2,b) ∈ JGk_TX2_Group0_02.group) :
    JGk_TX2_Group0_00.stream.idxOf (2,b)=24+JGk_TX2_Group0_02.group.idxOf (2,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (2,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (2,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (2,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (2,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (2,b) ∈ JGk_TX2_Group2_02.group) :
    JGk_TX2_Group2_00.stream.idxOf (2,b)=24+JGk_TX2_Group2_02.group.idxOf (2,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (2,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (2,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (2,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (2,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 2) :
    JGk_TX2_SiblingBase.native0 2 b=JGf_TX2_M0Roots.siblingAt 2 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14300 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,14300)=0 from rfl]
    exact JGh_TX2_Siblings02.k0c024_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21252 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,21252)=1 from rfl]
    exact JGh_TX2_Siblings02.k0c025_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42152 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,42152)=2 from rfl]
    exact JGh_TX2_Siblings02.k0c026_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55380 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,55380)=3 from rfl]
    exact JGh_TX2_Siblings02.k0c027_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63856 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,63856)=4 from rfl]
    exact JGh_TX2_Siblings02.k0c028_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132356 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,132356)=5 from rfl]
    exact JGh_TX2_Siblings02.k0c029_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149628 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,149628)=6 from rfl]
    exact JGh_TX2_Siblings02.k0c030_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166160 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,166160)=7 from rfl]
    exact JGh_TX2_Siblings02.k0c031_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178084 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,178084)=8 from rfl]
    exact JGh_TX2_Siblings02.k0c032_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179616 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,179616)=9 from rfl]
    exact JGh_TX2_Siblings02.k0c033_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185632 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,185632)=10 from rfl]
    exact JGh_TX2_Siblings02.k0c034_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218088 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,218088)=11 from rfl]
    exact JGh_TX2_Siblings02.k0c035_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 2) :
    JGk_TX2_SiblingBase.native1 2 b=JGh_TX2_M1Roots.siblingAt 2 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14300 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,14300)=0 from rfl]
    exact JGh_TX2_Siblings02.k1c024_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21252 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,21252)=1 from rfl]
    exact JGh_TX2_Siblings02.k1c025_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42152 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,42152)=2 from rfl]
    exact JGh_TX2_Siblings02.k1c026_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55380 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,55380)=3 from rfl]
    exact JGh_TX2_Siblings02.k1c027_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63856 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,63856)=4 from rfl]
    exact JGh_TX2_Siblings02.k1c028_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132356 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,132356)=5 from rfl]
    exact JGh_TX2_Siblings02.k1c029_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149628 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,149628)=6 from rfl]
    exact JGh_TX2_Siblings02.k1c030_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166160 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,166160)=7 from rfl]
    exact JGh_TX2_Siblings02.k1c031_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178084 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,178084)=8 from rfl]
    exact JGh_TX2_Siblings02.k1c032_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179616 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,179616)=9 from rfl]
    exact JGh_TX2_Siblings02.k1c033_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185632 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,185632)=10 from rfl]
    exact JGh_TX2_Siblings02.k1c034_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218088 (by decide)]
    rw [show JGk_TX2_Group0_02.group.idxOf (2,218088)=11 from rfl]
    exact JGh_TX2_Siblings02.k1c035_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 2) :
    JGk_TX2_SiblingBase.native2 2 b=JGc_TX2_M2Roots.siblingAt 2 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3568 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,3568)=0 from rfl]
    exact JGh_TX2_Siblings02.k2c024_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5316 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,5316)=1 from rfl]
    exact JGh_TX2_Siblings02.k2c025_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10540 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,10540)=2 from rfl]
    exact JGh_TX2_Siblings02.k2c026_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13840 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,13840)=3 from rfl]
    exact JGh_TX2_Siblings02.k2c027_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15960 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,15960)=4 from rfl]
    exact JGh_TX2_Siblings02.k2c028_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33092 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,33092)=5 from rfl]
    exact JGh_TX2_Siblings02.k2c029_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37400 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,37400)=6 from rfl]
    exact JGh_TX2_Siblings02.k2c030_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41536 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,41536)=7 from rfl]
    exact JGh_TX2_Siblings02.k2c031_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44524 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,44524)=8 from rfl]
    exact JGh_TX2_Siblings02.k2c032_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44908 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,44908)=9 from rfl]
    exact JGh_TX2_Siblings02.k2c033_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46412 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,46412)=10 from rfl]
    exact JGh_TX2_Siblings02.k2c034_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54524 (by decide)]
    rw [show JGk_TX2_Group2_02.group.idxOf (2,54524)=11 from rfl]
    exact JGh_TX2_Siblings02.k2c035_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup02
