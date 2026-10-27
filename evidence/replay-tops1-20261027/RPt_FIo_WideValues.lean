import RPt_FIo_QMValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_WideValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
def Canon (x : NE) : Prop := FIo_QMValues.Canon x.c0 ∧ FIo_QMValues.Canon x.c1

theorem add (x y z : NE) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z) :
    Canon z ∧ decodeWide (wide z)=decodeWide (wide x)+decodeWide (wide y) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.add at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NE)=z := Result.ok.inj run
  subst z
  have va := FIo_QMValues.add x.c0 y.c0 a hx.1 hy.1 ha
  have vb := FIo_QMValues.add x.c1 y.c1 b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

#print axioms add
end AspisR1.FIo_WideValues
end
