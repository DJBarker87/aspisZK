import Port5Q1_Domain
set_option autoImplicit false
namespace AspisR1.Port5Q1_DomainLanes

theorem x (u : Nat) : (Port5Q1_Domain.words u)[2]?.getD 0=FoldGeometryBridge.lx (Port5Q1_Domain.parent u) := by
  rfl
theorem y (u : Nat) : (Port5Q1_Domain.words u)[3]?.getD 0=FoldGeometryBridge.ly (Port5Q1_Domain.parent u) := by
  rfl
theorem z (u : Nat) : (Port5Q1_Domain.words u)[4]?.getD 0=FoldGeometryBridge.lz (Port5Q1_Domain.parent u) := by
  rfl

#print axioms x
#print axioms y
#print axioms z
end AspisR1.Port5Q1_DomainLanes
