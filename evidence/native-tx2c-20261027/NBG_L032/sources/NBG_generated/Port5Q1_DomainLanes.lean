import Port5Q1_FiveCells
set_option autoImplicit false
namespace AspisR1.Port5Q1_DomainLanes

theorem x (u : Nat) : (Port5Q1_Domain.words u)[2]?.getD 0=FoldGeometryBridge.lx (Port5Q1_Domain.parent u) := by
  unfold Port5Q1_Domain.words
  exact Port5Q1_FiveCells.third _ _ _ _ _
theorem y (u : Nat) : (Port5Q1_Domain.words u)[3]?.getD 0=FoldGeometryBridge.ly (Port5Q1_Domain.parent u) := by
  unfold Port5Q1_Domain.words
  exact Port5Q1_FiveCells.fourth _ _ _ _ _
theorem z (u : Nat) : (Port5Q1_Domain.words u)[4]?.getD 0=FoldGeometryBridge.lz (Port5Q1_Domain.parent u) := by
  unfold Port5Q1_Domain.words
  exact Port5Q1_FiveCells.fifth _ _ _ _ _

#print axioms x
#print axioms y
#print axioms z
end AspisR1.Port5Q1_DomainLanes
