import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup11
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (11,b) ∈ JGk_TX2_Group0_11.group) :
    JGk_TX2_Group0_00.stream.idxOf (11,b)=132+JGk_TX2_Group0_11.group.idxOf (11,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_00.group from by
    intro hm
    have e := JGk_TX2_Group0_00.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_01.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_01.group from by
    intro hm
    have e := JGk_TX2_Group0_01.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_02.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_02.group from by
    intro hm
    have e := JGk_TX2_Group0_02.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_03.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_03.group from by
    intro hm
    have e := JGk_TX2_Group0_03.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_04.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_04.group from by
    intro hm
    have e := JGk_TX2_Group0_04.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_05.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_05.group from by
    intro hm
    have e := JGk_TX2_Group0_05.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_06.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_06.group from by
    intro hm
    have e := JGk_TX2_Group0_06.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_07.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_07.group from by
    intro hm
    have e := JGk_TX2_Group0_07.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_08.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_08.group from by
    intro hm
    have e := JGk_TX2_Group0_08.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_09.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_09.group from by
    intro hm
    have e := JGk_TX2_Group0_09.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_10.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group0_10.group from by
    intro hm
    have e := JGk_TX2_Group0_10.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group0_11.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group0_00.group.length=12 from rfl,show JGk_TX2_Group0_01.group.length=12 from rfl,show JGk_TX2_Group0_02.group.length=12 from rfl,show JGk_TX2_Group0_03.group.length=12 from rfl,show JGk_TX2_Group0_04.group.length=12 from rfl,show JGk_TX2_Group0_05.group.length=12 from rfl,show JGk_TX2_Group0_06.group.length=12 from rfl,show JGk_TX2_Group0_07.group.length=12 from rfl,show JGk_TX2_Group0_08.group.length=12 from rfl,show JGk_TX2_Group0_09.group.length=12 from rfl,show JGk_TX2_Group0_10.group.length=12 from rfl]
  all_goals omega
#print axioms offset0
theorem offset2 (b : Nat) (hb : (11,b) ∈ JGk_TX2_Group2_11.group) :
    JGk_TX2_Group2_00.stream.idxOf (11,b)=129+JGk_TX2_Group2_11.group.idxOf (11,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_00.group from by
    intro hm
    have e := JGk_TX2_Group2_00.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_01.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_01.group from by
    intro hm
    have e := JGk_TX2_Group2_01.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_02.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_02.group from by
    intro hm
    have e := JGk_TX2_Group2_02.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_03.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_03.group from by
    intro hm
    have e := JGk_TX2_Group2_03.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_04.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_04.group from by
    intro hm
    have e := JGk_TX2_Group2_04.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_05.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_05.group from by
    intro hm
    have e := JGk_TX2_Group2_05.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_06.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_06.group from by
    intro hm
    have e := JGk_TX2_Group2_06.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_07.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_07.group from by
    intro hm
    have e := JGk_TX2_Group2_07.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_08.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_08.group from by
    intro hm
    have e := JGk_TX2_Group2_08.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_09.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_09.group from by
    intro hm
    have e := JGk_TX2_Group2_09.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_10.stream,List.idxOf_append_of_notMem (show (11,b) ∉ JGk_TX2_Group2_10.group from by
    intro hm
    have e := JGk_TX2_Group2_10.height (11,b) hm
    contradiction)]
  rw [JGk_TX2_Group2_11.stream,List.idxOf_append_of_mem hb]
  simp only [show JGk_TX2_Group2_00.group.length=12 from rfl,show JGk_TX2_Group2_01.group.length=12 from rfl,show JGk_TX2_Group2_02.group.length=12 from rfl,show JGk_TX2_Group2_03.group.length=12 from rfl,show JGk_TX2_Group2_04.group.length=12 from rfl,show JGk_TX2_Group2_05.group.length=12 from rfl,show JGk_TX2_Group2_06.group.length=12 from rfl,show JGk_TX2_Group2_07.group.length=12 from rfl,show JGk_TX2_Group2_08.group.length=12 from rfl,show JGk_TX2_Group2_09.group.length=10 from rfl,show JGk_TX2_Group2_10.group.length=11 from rfl]
  all_goals omega
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 11) :
    JGk_TX2_SiblingBase.native0 11 b=JGf_TX2_M0Roots.siblingAt 11 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14336 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,14336)=0 from rfl]
    exact JGh_TX2_Siblings11.k0c132_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 22528 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,22528)=1 from rfl]
    exact JGh_TX2_Siblings11.k0c133_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 43008 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,43008)=2 from rfl]
    exact JGh_TX2_Siblings11.k0c134_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 53248 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,53248)=3 from rfl]
    exact JGh_TX2_Siblings11.k0c135_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 61440 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,61440)=4 from rfl]
    exact JGh_TX2_Siblings11.k0c136_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 133120 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,133120)=5 from rfl]
    exact JGh_TX2_Siblings11.k0c137_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 147456 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,147456)=6 from rfl]
    exact JGh_TX2_Siblings11.k0c138_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 163840 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,163840)=7 from rfl]
    exact JGh_TX2_Siblings11.k0c139_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 186368 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,186368)=8 from rfl]
    exact JGh_TX2_Siblings11.k0c140_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 219136 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,219136)=9 from rfl]
    exact JGh_TX2_Siblings11.k0c141_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 11) :
    JGk_TX2_SiblingBase.native1 11 b=JGh_TX2_M1Roots.siblingAt 11 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14336 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,14336)=0 from rfl]
    exact JGh_TX2_Siblings11.k1c132_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 22528 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,22528)=1 from rfl]
    exact JGh_TX2_Siblings11.k1c133_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 43008 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,43008)=2 from rfl]
    exact JGh_TX2_Siblings11.k1c134_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 53248 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,53248)=3 from rfl]
    exact JGh_TX2_Siblings11.k1c135_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 61440 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,61440)=4 from rfl]
    exact JGh_TX2_Siblings11.k1c136_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 133120 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,133120)=5 from rfl]
    exact JGh_TX2_Siblings11.k1c137_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 147456 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,147456)=6 from rfl]
    exact JGh_TX2_Siblings11.k1c138_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 163840 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,163840)=7 from rfl]
    exact JGh_TX2_Siblings11.k1c139_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 186368 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,186368)=8 from rfl]
    exact JGh_TX2_Siblings11.k1c140_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 219136 (by decide)]
    rw [show JGk_TX2_Group0_11.group.idxOf (11,219136)=9 from rfl]
    exact JGh_TX2_Siblings11.k1c141_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 11) :
    JGk_TX2_SiblingBase.native2 11 b=JGc_TX2_M2Roots.siblingAt 11 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 0 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,0)=0 from rfl]
    exact JGh_TX2_Siblings11.k2c129_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 6144 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,6144)=1 from rfl]
    exact JGh_TX2_Siblings11.k2c130_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 8192 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,8192)=2 from rfl]
    exact JGh_TX2_Siblings11.k2c131_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 34816 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,34816)=3 from rfl]
    exact JGh_TX2_Siblings11.k2c132_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 38912 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,38912)=4 from rfl]
    exact JGh_TX2_Siblings11.k2c133_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 47104 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,47104)=5 from rfl]
    exact JGh_TX2_Siblings11.k2c134_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 55296 (by decide)]
    rw [show JGk_TX2_Group2_11.group.idxOf (11,55296)=6 from rfl]
    exact JGh_TX2_Siblings11.k2c135_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup11
