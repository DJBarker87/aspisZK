import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup01
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (1,b) ∈ JGk_TX2_Group0_01.group) :
    JGk_TX2_Group0_00.stream.idxOf (1,b)=12+JGk_TX2_Group0_01.group.idxOf (1,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (1,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (1,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (1,b) ∈ JGk_TX2_Group2_01.group) :
    JGk_TX2_Group2_00.stream.idxOf (1,b)=12+JGk_TX2_Group2_01.group.idxOf (1,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (1,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (1,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 1) :
    JGk_TX2_SiblingBase.native0 1 b=JGf_TX2_M0Roots.siblingAt 1 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14298 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,14298)=0 from rfl]
    exact JGh_TX2_Siblings01.k0c012_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21250 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,21250)=1 from rfl]
    exact JGh_TX2_Siblings01.k0c013_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42156 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,42156)=2 from rfl]
    exact JGh_TX2_Siblings01.k0c014_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55378 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,55378)=3 from rfl]
    exact JGh_TX2_Siblings01.k0c015_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63862 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,63862)=4 from rfl]
    exact JGh_TX2_Siblings01.k0c016_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132352 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,132352)=5 from rfl]
    exact JGh_TX2_Siblings01.k0c017_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149626 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,149626)=6 from rfl]
    exact JGh_TX2_Siblings01.k0c018_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166166 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,166166)=7 from rfl]
    exact JGh_TX2_Siblings01.k0c019_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178082 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,178082)=8 from rfl]
    exact JGh_TX2_Siblings01.k0c020_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179620 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,179620)=9 from rfl]
    exact JGh_TX2_Siblings01.k0c021_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185638 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,185638)=10 from rfl]
    exact JGh_TX2_Siblings01.k0c022_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218092 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,218092)=11 from rfl]
    exact JGh_TX2_Siblings01.k0c023_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 1) :
    JGk_TX2_SiblingBase.native1 1 b=JGh_TX2_M1Roots.siblingAt 1 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14298 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,14298)=0 from rfl]
    exact JGh_TX2_Siblings01.k1c012_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21250 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,21250)=1 from rfl]
    exact JGh_TX2_Siblings01.k1c013_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42156 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,42156)=2 from rfl]
    exact JGh_TX2_Siblings01.k1c014_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55378 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,55378)=3 from rfl]
    exact JGh_TX2_Siblings01.k1c015_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63862 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,63862)=4 from rfl]
    exact JGh_TX2_Siblings01.k1c016_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132352 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,132352)=5 from rfl]
    exact JGh_TX2_Siblings01.k1c017_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149626 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,149626)=6 from rfl]
    exact JGh_TX2_Siblings01.k1c018_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166166 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,166166)=7 from rfl]
    exact JGh_TX2_Siblings01.k1c019_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178082 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,178082)=8 from rfl]
    exact JGh_TX2_Siblings01.k1c020_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179620 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,179620)=9 from rfl]
    exact JGh_TX2_Siblings01.k1c021_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185638 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,185638)=10 from rfl]
    exact JGh_TX2_Siblings01.k1c022_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218092 (by decide)]
    rw [show JGk_TX2_Group0_01.group.idxOf (1,218092)=11 from rfl]
    exact JGh_TX2_Siblings01.k1c023_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 1) :
    JGk_TX2_SiblingBase.native2 1 b=JGc_TX2_M2Roots.siblingAt 1 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3572 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,3572)=0 from rfl]
    exact JGh_TX2_Siblings01.k2c012_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5314 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,5314)=1 from rfl]
    exact JGh_TX2_Siblings01.k2c013_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10536 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,10536)=2 from rfl]
    exact JGh_TX2_Siblings01.k2c014_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13846 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,13846)=3 from rfl]
    exact JGh_TX2_Siblings01.k2c015_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15966 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,15966)=4 from rfl]
    exact JGh_TX2_Siblings01.k2c016_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33090 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,33090)=5 from rfl]
    exact JGh_TX2_Siblings01.k2c017_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37404 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,37404)=6 from rfl]
    exact JGh_TX2_Siblings01.k2c018_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41542 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,41542)=7 from rfl]
    exact JGh_TX2_Siblings01.k2c019_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44522 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,44522)=8 from rfl]
    exact JGh_TX2_Siblings01.k2c020_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44906 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,44906)=9 from rfl]
    exact JGh_TX2_Siblings01.k2c021_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46410 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,46410)=10 from rfl]
    exact JGh_TX2_Siblings01.k2c022_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54520 (by decide)]
    rw [show JGk_TX2_Group2_01.group.idxOf (1,54520)=11 from rfl]
    exact JGh_TX2_Siblings01.k2c023_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup01
