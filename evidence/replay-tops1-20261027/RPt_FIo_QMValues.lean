import RPt_FIo_CMValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_QMValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
def Canon (x : NQ) : Prop := FIo_CMValues.Canon x.c0 ∧ FIo_CMValues.Canon x.c1

theorem add (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.QM31.add x y=ok z) :
    Canon z ∧ decodeQM (qm z)=decodeQM (qm x)+decodeQM (qm y) := by
  unfold FIo_Native.aspis_core.field.QM31.add at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NQ)=z := Result.ok.inj run
  subst z
  have va := FIo_CMValues.add x.c0 y.c0 a hx.1 hy.1 ha
  have vb := FIo_CMValues.add x.c1 y.c1 b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

theorem sub (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIo_Native.aspis_core.field.QM31.sub x y=ok z) :
    Canon z ∧ decodeQM (qm z)=decodeQM (qm x)-decodeQM (qm y) := by
  unfold FIo_Native.aspis_core.field.QM31.sub at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NQ)=z := Result.ok.inj run
  subst z
  have va := FIo_CMValues.sub x.c0 y.c0 a hx.1 hy.1 ha
  have vb := FIo_CMValues.sub x.c1 y.c1 b hx.2 hy.2 hb
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2

#print axioms add
#print axioms sub
end AspisR1.FIo_QMValues
end
