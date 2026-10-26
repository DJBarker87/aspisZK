import FIo_CMProduct
import FIo_ReduceValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_CMMulValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC cm)
open FIo_CMValues (Canon)

theorem mul (x y z : NC) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.CM31.mul x y=ok z) :
    Canon z ∧ decodeC (cm z)=decodeC (cm x)*decodeC (cm y) := by
  unfold FIo_Native.aspis_core.field.CM31.mul at run
  obtain ⟨m0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨m2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,c⟩ : NC)=z := Result.ok.inj run
  subst z
  have v0 := FIo_M31Values.mul x.a y.a m0 h0
  have v1 := FIo_M31Values.mul x.b y.b m1 h1
  have can2 := (FIo_ReduceValues.m31_value (FIo_CMProduct.cross x y) m2 h2).2
  have val2 := FIo_ReduceValues.field_value (FIo_CMProduct.cross x y) m2 h2
  rw [FIo_CMProduct.cross_value x y hx hy] at val2
  have cross : decodeM m2=(decodeM x.a+decodeM x.b)*(decodeM y.a+decodeM y.b) := by
    simpa only [decodeM,Nat.cast_add,Nat.cast_mul] using val2
  have va := FIo_M31Values.sub m0 m1 a v0.1 v1.1 ha
  have vb := FIo_M31Values.sub m2 m0 b can2 v0.1 hb
  have vc := FIo_M31Values.sub b m1 c vb.1 v1.1 hc
  refine ⟨⟨va.1,vc.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeM a=decodeM x.a*decodeM y.a+(-1)*decodeM x.b*decodeM y.b
    rw [va.2,v0.2,v1.2]
    ring
  · change decodeM c=decodeM x.a*decodeM y.b+decodeM x.b*decodeM y.a
    rw [vc.2,vb.2,cross,v0.2,v1.2]
    ring

#print axioms mul
end AspisR1.FIo_CMMulValues
end
