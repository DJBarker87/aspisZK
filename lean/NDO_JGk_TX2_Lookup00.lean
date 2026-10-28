import NDO_JGk_TX2_SiblingBase
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Lookup00
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
theorem offset0 (b : Nat) (hb : (0,b) ∈ JGk_TX2_Group0_00.group) :
    JGk_TX2_Group0_00.stream.idxOf (0,b)=0+JGk_TX2_Group0_00.group.idxOf (0,b) := by
  rw [JGk_TX2_Group0_00.stream,List.idxOf_append_of_mem hb]
  simp only [Nat.zero_add]
#print axioms offset0
theorem offset2 (b : Nat) (hb : (0,b) ∈ JGk_TX2_Group2_00.group) :
    JGk_TX2_Group2_00.stream.idxOf (0,b)=0+JGk_TX2_Group2_00.group.idxOf (0,b) := by
  rw [JGk_TX2_Group2_00.stream,List.idxOf_append_of_mem hb]
  simp only [Nat.zero_add]
#print axioms offset2
theorem source0 (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases 0) :
    JGk_TX2_SiblingBase.native0 0 b=JGf_TX2_M0Roots.siblingAt 0 b := by
  simp only [JGf_TX2_M0Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 14296 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,14296)=0 from rfl]
    exact JGh_TX2_Siblings00.k0c000_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 21249 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,21249)=1 from rfl]
    exact JGh_TX2_Siblings00.k0c001_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 42159 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,42159)=2 from rfl]
    exact JGh_TX2_Siblings00.k0c002_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 55376 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,55376)=3 from rfl]
    exact JGh_TX2_Siblings00.k0c003_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 63861 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,63861)=4 from rfl]
    exact JGh_TX2_Siblings00.k0c004_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 132354 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,132354)=5 from rfl]
    exact JGh_TX2_Siblings00.k0c005_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 149625 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,149625)=6 from rfl]
    exact JGh_TX2_Siblings00.k0c006_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 166164 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,166164)=7 from rfl]
    exact JGh_TX2_Siblings00.k0c007_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 178081 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,178081)=8 from rfl]
    exact JGh_TX2_Siblings00.k0c008_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 179623 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,179623)=9 from rfl]
    exact JGh_TX2_Siblings00.k0c009_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 185636 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,185636)=10 from rfl]
    exact JGh_TX2_Siblings00.k0c010_read
  · unfold JGk_TX2_SiblingBase.native0
    rw [offset0 218095 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,218095)=11 from rfl]
    exact JGh_TX2_Siblings00.k0c011_read
#print axioms source0
theorem source1 (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases 0) :
    JGk_TX2_SiblingBase.native1 0 b=JGh_TX2_M1Roots.siblingAt 0 b := by
  simp only [JGh_TX2_M1Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 14296 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,14296)=0 from rfl]
    exact JGh_TX2_Siblings00.k1c000_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 21249 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,21249)=1 from rfl]
    exact JGh_TX2_Siblings00.k1c001_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 42159 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,42159)=2 from rfl]
    exact JGh_TX2_Siblings00.k1c002_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 55376 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,55376)=3 from rfl]
    exact JGh_TX2_Siblings00.k1c003_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 63861 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,63861)=4 from rfl]
    exact JGh_TX2_Siblings00.k1c004_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 132354 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,132354)=5 from rfl]
    exact JGh_TX2_Siblings00.k1c005_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 149625 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,149625)=6 from rfl]
    exact JGh_TX2_Siblings00.k1c006_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 166164 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,166164)=7 from rfl]
    exact JGh_TX2_Siblings00.k1c007_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 178081 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,178081)=8 from rfl]
    exact JGh_TX2_Siblings00.k1c008_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 179623 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,179623)=9 from rfl]
    exact JGh_TX2_Siblings00.k1c009_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 185636 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,185636)=10 from rfl]
    exact JGh_TX2_Siblings00.k1c010_read
  · unfold JGk_TX2_SiblingBase.native1
    rw [offset0 218095 (by decide)]
    rw [show JGk_TX2_Group0_00.group.idxOf (0,218095)=11 from rfl]
    exact JGh_TX2_Siblings00.k1c011_read
#print axioms source1
theorem source2 (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases 0) :
    JGk_TX2_SiblingBase.native2 0 b=JGc_TX2_M2Roots.siblingAt 0 b := by
  simp only [JGc_TX2_M2Roots.bases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 3575 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,3575)=0 from rfl]
    exact JGh_TX2_Siblings00.k2c000_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 5313 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,5313)=1 from rfl]
    exact JGh_TX2_Siblings00.k2c001_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 10538 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,10538)=2 from rfl]
    exact JGh_TX2_Siblings00.k2c002_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 13845 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,13845)=3 from rfl]
    exact JGh_TX2_Siblings00.k2c003_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 15964 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,15964)=4 from rfl]
    exact JGh_TX2_Siblings00.k2c004_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 33089 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,33089)=5 from rfl]
    exact JGh_TX2_Siblings00.k2c005_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 37407 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,37407)=6 from rfl]
    exact JGh_TX2_Siblings00.k2c006_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 41540 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,41540)=7 from rfl]
    exact JGh_TX2_Siblings00.k2c007_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44521 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,44521)=8 from rfl]
    exact JGh_TX2_Siblings00.k2c008_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 44904 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,44904)=9 from rfl]
    exact JGh_TX2_Siblings00.k2c009_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 46408 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,46408)=10 from rfl]
    exact JGh_TX2_Siblings00.k2c010_read
  · unfold JGk_TX2_SiblingBase.native2
    rw [offset2 54522 (by decide)]
    rw [show JGk_TX2_Group2_00.group.idxOf (0,54522)=11 from rfl]
    exact JGh_TX2_Siblings00.k2c011_read
#print axioms source2
end AspisR1.JGk_TX2_Lookup00
