import NDO_JFv_TX2_CircleGeometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Query0Inverse
open Aeneas Aeneas.Std
abbrev FP := Port5Q1_QueryPorts.FP

theorem reciprocal (a b : Nat) (h : a*b%2147483647=1) :
    (a : FP)⁻¹=(b : FP) := by
  apply inv_eq_of_mul_eq_one_left
  change (b : ZMod 2147483647)*(a : ZMod 2147483647)=1
  rw [←Nat.cast_mul,←ZMod.natCast_mod (b*a) 2147483647,Nat.mul_comm b a,h]
  rfl

theorem x : (S7JoinBasisMachine.decode JFv_TX2_Row10.value.x)⁻¹=(243259912 : FP) := by
  exact reciprocal 774039344 243259912 (by norm_num)

theorem y : (S7JoinBasisMachine.decode JFv_TX2_Row10.value.y)⁻¹=(1029545577 : FP) := by
  exact reciprocal 1196781258 1029545577 (by norm_num)

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane (JFv_TX2_CircleGeometry.inverse err seed 0) 0)=243259912 ∧
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane (JFv_TX2_CircleGeometry.inverse err seed 0) 1)=1029545577 := by
  constructor
  · exact (JFv_TX2_CircleGeometry.decoded err seed 0 0).trans x
  · exact (JFv_TX2_CircleGeometry.decoded err seed 0 1).trans y
#print axioms reciprocal
#print axioms x
#print axioms y
#print axioms source
end AspisR1.JFv_TX2_Query0Inverse
end
