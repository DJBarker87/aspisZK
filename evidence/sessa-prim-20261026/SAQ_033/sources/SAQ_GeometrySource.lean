import SAQ_Domain
import SAQ_Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_GeometrySource
open Aeneas Aeneas.Std Result

def install {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    Port3_NativeGeometryBody.Ops C :=
  {SAQ_Geometry.install ops with op11 := SAQ_Inverse.source}

structure Remaining {C : Type} (ops : Port3_NativeGeometryBody.Ops C) : Prop where
  fibre : ∀ u f, ops.op12 u=ok (.Ok f) → f=u ∧ f.val<262144

theorem canonical {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops) :=
  let h := SAQ_Geometry.canonical ops
  ⟨h.point,h.line,h.multiply,h.double,h.one,h.subtract⟩

theorem domain {C : Type} (ops : Port3_NativeGeometryBody.Ops C)
    (rest : Remaining (install ops)) : Port5Q1_Domain.SessionADomain (install ops) := by
  constructor
  · exact rest.fibre
  · exact SAQ_Domain.point ops
  · exact SAQ_Domain.line ops
  · intro x y z run
    exact R17CurrentM31Semantics.current_mul_decode x y z run
  · intro x y run
    have h := R17CurrentM31Semantics.current_add_decode x x y run
    change S7JoinBasisMachine.decode y=2*S7JoinBasisMachine.decode x
    change S7JoinBasisMachine.decode y=S7JoinBasisMachine.decode x+S7JoinBasisMachine.decode x at h
    rw [h]; ring
  · intro x run
    have same : 1#u32=x := Result.ok.inj run
    subst x
    rfl
  · intro x y z run
    exact R17CurrentM31Semantics.current_sub_decode x y z run

theorem multiply {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    (install ops).op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := rfl

theorem one {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    (install ops).op7=ok 1#u32 := rfl

theorem inverse {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    (install ops).op11=Port4C_InverseExecution.inverse_owned :=
  SAQ_Inverse.source_eq_reference

#print axioms canonical
#print axioms domain
#print axioms multiply
#print axioms one
#print axioms inverse
end AspisR1.SAQ_GeometrySource
end
