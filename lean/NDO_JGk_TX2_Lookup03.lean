import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup03
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (3,b) ∈ JGk_TX2_Group0_03.group) :
    JGk_TX2_Group0_00.stream.idxOf (3,b)=36+JGk_TX2_Group0_03.group.idxOf (3,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (3,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (3,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (3,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (3,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (3,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (3,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (3,b) ∈ JGk_TX2_Group2_03.group) :
    JGk_TX2_Group2_00.stream.idxOf (3,b)=36+JGk_TX2_Group2_03.group.idxOf (3,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (3,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (3,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (3,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (3,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (3,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (3,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 3) :
    JGk_TX2_SiblingBase.native0 3 b=JGf_TX2_M0Roots.siblingAt 3 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14288 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,14288)=0 from rfl]
    exact JGh_TX2_Siblings03.k0c036_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21256 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,21256)=1 from rfl]
    exact JGh_TX2_Siblings03.k0c037_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42144 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,42144)=2 from rfl]
    exact JGh_TX2_Siblings03.k0c038_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55384 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,55384)=3 from rfl]
    exact JGh_TX2_Siblings03.k0c039_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63864 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,63864)=4 from rfl]
    exact JGh_TX2_Siblings03.k0c040_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132360 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,132360)=5 from rfl]
    exact JGh_TX2_Siblings03.k0c041_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149616 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,149616)=6 from rfl]
    exact JGh_TX2_Siblings03.k0c042_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166168 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,166168)=7 from rfl]
    exact JGh_TX2_Siblings03.k0c043_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178088 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,178088)=8 from rfl]
    exact JGh_TX2_Siblings03.k0c044_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179624 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,179624)=9 from rfl]
    exact JGh_TX2_Siblings03.k0c045_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185640 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,185640)=10 from rfl]
    exact JGh_TX2_Siblings03.k0c046_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218080 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,218080)=11 from rfl]
    exact JGh_TX2_Siblings03.k0c047_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 3) :
    JGk_TX2_SiblingBase.native1 3 b=JGh_TX2_M1Roots.siblingAt 3 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14288 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,14288)=0 from rfl]
    exact JGh_TX2_Siblings03.k1c036_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21256 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,21256)=1 from rfl]
    exact JGh_TX2_Siblings03.k1c037_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42144 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,42144)=2 from rfl]
    exact JGh_TX2_Siblings03.k1c038_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55384 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,55384)=3 from rfl]
    exact JGh_TX2_Siblings03.k1c039_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63864 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,63864)=4 from rfl]
    exact JGh_TX2_Siblings03.k1c040_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132360 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,132360)=5 from rfl]
    exact JGh_TX2_Siblings03.k1c041_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149616 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,149616)=6 from rfl]
    exact JGh_TX2_Siblings03.k1c042_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166168 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,166168)=7 from rfl]
    exact JGh_TX2_Siblings03.k1c043_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178088 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,178088)=8 from rfl]
    exact JGh_TX2_Siblings03.k1c044_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179624 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,179624)=9 from rfl]
    exact JGh_TX2_Siblings03.k1c045_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185640 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,185640)=10 from rfl]
    exact JGh_TX2_Siblings03.k1c046_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218080 (by decide)]
    rw [show JGk_TX2_Group0_03.group.idxOf (3,218080)=11 from rfl]
    exact JGh_TX2_Siblings03.k1c047_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 3) :
    JGk_TX2_SiblingBase.native2 3 b=JGc_TX2_M2Roots.siblingAt 3 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3576 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,3576)=0 from rfl]
    exact JGh_TX2_Siblings03.k2c036_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5320 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,5320)=1 from rfl]
    exact JGh_TX2_Siblings03.k2c037_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10528 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,10528)=2 from rfl]
    exact JGh_TX2_Siblings03.k2c038_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13848 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,13848)=3 from rfl]
    exact JGh_TX2_Siblings03.k2c039_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15952 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,15952)=4 from rfl]
    exact JGh_TX2_Siblings03.k2c040_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33096 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,33096)=5 from rfl]
    exact JGh_TX2_Siblings03.k2c041_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37392 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,37392)=6 from rfl]
    exact JGh_TX2_Siblings03.k2c042_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41544 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,41544)=7 from rfl]
    exact JGh_TX2_Siblings03.k2c043_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44512 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,44512)=8 from rfl]
    exact JGh_TX2_Siblings03.k2c044_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44896 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,44896)=9 from rfl]
    exact JGh_TX2_Siblings03.k2c045_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46400 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,46400)=10 from rfl]
    exact JGh_TX2_Siblings03.k2c046_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54512 (by decide)]
    rw [show JGk_TX2_Group2_03.group.idxOf (3,54512)=11 from rfl]
    exact JGh_TX2_Siblings03.k2c047_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup03
