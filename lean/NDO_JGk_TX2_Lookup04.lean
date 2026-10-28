import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup04
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (4,b) ∈ JGk_TX2_Group0_04.group) :
    JGk_TX2_Group0_00.stream.idxOf (4,b)=48+JGk_TX2_Group0_04.group.idxOf (4,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (4,b) ∈ JGk_TX2_Group2_04.group) :
    JGk_TX2_Group2_00.stream.idxOf (4,b)=48+JGk_TX2_Group2_04.group.idxOf (4,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (4,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (4,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 4) :
    JGk_TX2_SiblingBase.native0 4 b=JGf_TX2_M0Roots.siblingAt 4 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14272 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,14272)=0 from rfl]
    exact JGh_TX2_Siblings04.k0c048_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21264 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,21264)=1 from rfl]
    exact JGh_TX2_Siblings04.k0c049_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42160 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,42160)=2 from rfl]
    exact JGh_TX2_Siblings04.k0c050_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55360 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,55360)=3 from rfl]
    exact JGh_TX2_Siblings04.k0c051_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63840 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,63840)=4 from rfl]
    exact JGh_TX2_Siblings04.k0c052_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132368 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,132368)=5 from rfl]
    exact JGh_TX2_Siblings04.k0c053_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149600 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,149600)=6 from rfl]
    exact JGh_TX2_Siblings04.k0c054_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166144 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,166144)=7 from rfl]
    exact JGh_TX2_Siblings04.k0c055_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178096 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,178096)=8 from rfl]
    exact JGh_TX2_Siblings04.k0c056_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179632 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,179632)=9 from rfl]
    exact JGh_TX2_Siblings04.k0c057_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185648 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,185648)=10 from rfl]
    exact JGh_TX2_Siblings04.k0c058_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218096 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,218096)=11 from rfl]
    exact JGh_TX2_Siblings04.k0c059_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 4) :
    JGk_TX2_SiblingBase.native1 4 b=JGh_TX2_M1Roots.siblingAt 4 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14272 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,14272)=0 from rfl]
    exact JGh_TX2_Siblings04.k1c048_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21264 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,21264)=1 from rfl]
    exact JGh_TX2_Siblings04.k1c049_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42160 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,42160)=2 from rfl]
    exact JGh_TX2_Siblings04.k1c050_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55360 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,55360)=3 from rfl]
    exact JGh_TX2_Siblings04.k1c051_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63840 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,63840)=4 from rfl]
    exact JGh_TX2_Siblings04.k1c052_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132368 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,132368)=5 from rfl]
    exact JGh_TX2_Siblings04.k1c053_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149600 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,149600)=6 from rfl]
    exact JGh_TX2_Siblings04.k1c054_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166144 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,166144)=7 from rfl]
    exact JGh_TX2_Siblings04.k1c055_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178096 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,178096)=8 from rfl]
    exact JGh_TX2_Siblings04.k1c056_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179632 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,179632)=9 from rfl]
    exact JGh_TX2_Siblings04.k1c057_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185648 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,185648)=10 from rfl]
    exact JGh_TX2_Siblings04.k1c058_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218096 (by decide)]
    rw [show JGk_TX2_Group0_04.group.idxOf (4,218096)=11 from rfl]
    exact JGh_TX2_Siblings04.k1c059_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 4) :
    JGk_TX2_SiblingBase.native2 4 b=JGc_TX2_M2Roots.siblingAt 4 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3552 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,3552)=0 from rfl]
    exact JGh_TX2_Siblings04.k2c048_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5328 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,5328)=1 from rfl]
    exact JGh_TX2_Siblings04.k2c049_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10544 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,10544)=2 from rfl]
    exact JGh_TX2_Siblings04.k2c050_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13824 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,13824)=3 from rfl]
    exact JGh_TX2_Siblings04.k2c051_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15936 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,15936)=4 from rfl]
    exact JGh_TX2_Siblings04.k2c052_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33104 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,33104)=5 from rfl]
    exact JGh_TX2_Siblings04.k2c053_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37376 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,37376)=6 from rfl]
    exact JGh_TX2_Siblings04.k2c054_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41552 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,41552)=7 from rfl]
    exact JGh_TX2_Siblings04.k2c055_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44528 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,44528)=8 from rfl]
    exact JGh_TX2_Siblings04.k2c056_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44912 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,44912)=9 from rfl]
    exact JGh_TX2_Siblings04.k2c057_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46416 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,46416)=10 from rfl]
    exact JGh_TX2_Siblings04.k2c058_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54496 (by decide)]
    rw [show JGk_TX2_Group2_04.group.idxOf (4,54496)=11 from rfl]
    exact JGh_TX2_Siblings04.k2c059_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup04
