import RPt_FIo_M31Values
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_CMValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC cm)
def Canon (x : NC) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647

theorem add (x y z : NC) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.CM31.add x y=ok z) :
    Canon z ∧ decodeC (cm z)=decodeC (cm x)+decodeC (cm y) := by
  unfold FIo_Native.aspis_core.field.CM31.add at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NC)=z := Result.ok.inj run
  subst z
  have va := FIo_M31Values.add x.a y.a a hx.1 hy.1 ha
  have vb := FIo_M31Values.add x.b y.b b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

theorem sub (x y z : NC) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.CM31.sub x y=ok z) :
    Canon z ∧ decodeC (cm z)=decodeC (cm x)-decodeC (cm y) := by
  unfold FIo_Native.aspis_core.field.CM31.sub at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NC)=z := Result.ok.inj run
  subst z
  have va := FIo_M31Values.sub x.a y.a a hx.1 hy.1 ha
  have vb := FIo_M31Values.sub x.b y.b b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

#print axioms add
#print axioms sub
end AspisR1.FIo_CMValues
end
