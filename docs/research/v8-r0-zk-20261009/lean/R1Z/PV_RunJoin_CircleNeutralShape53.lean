import R1Z.PV_RunJoin_CircleNeutralBase52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralShape53
def Canon (a : U32) : Prop := a.val < 2147483647
def CC (a : U32 × U32) : Prop := Canon a.1 ∧ Canon a.2
def QC (a : (U32 × U32) × (U32 × U32)) : Prop := CC a.1 ∧ CC a.2

theorem zero : Canon 0#u32 := by unfold Canon; decide
theorem one : Canon 1#u32 := by unfold Canon; decide
theorem czero : CC (0#u32,0#u32) := ⟨zero,zero⟩
theorem cone : CC (1#u32,0#u32) := ⟨one,zero⟩
theorem qzero : QC PV_RunJoin_CircleRawTower52.field.QM31.ZERO := ⟨czero,czero⟩
theorem qone : QC PV_RunJoin_CircleRawTower52.field.QM31.ONE := ⟨cone,czero⟩

#print axioms Canon
#print axioms CC
#print axioms QC
#print axioms zero
#print axioms one
#print axioms czero
#print axioms cone
#print axioms qzero
#print axioms qone
end R1Z.PV_RunJoin_CircleNeutralShape53
