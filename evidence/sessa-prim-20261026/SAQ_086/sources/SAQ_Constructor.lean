import SAQ_GeometrySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Constructor
open Aeneas Aeneas.Std Result

/-- Exact index_type! constructor body. The opaque CoreError carrier's
IndexOutOfRange constructor is a data parameter, never a correctness law. -/
def fibre {C : Type} (indexError : C) (u : Usize) : Result (core.result.Result Usize C) :=
  if u<262144#usize then ok (.Ok u) else ok (.Err indexError)

theorem fibre_law {C : Type} (indexError : C) (u f : Usize)
    (h : fibre indexError u=ok (.Ok f)) : f=u ∧ f.val<262144 := by
  unfold fibre at h
  split at h
  · rename_i bound
    have same : u=f := core.result.Result.Ok.inj (Result.ok.inj h)
    subst f
    exact ⟨rfl,bound⟩
  · cases h

def install {C : Type} (indexError : C) (ops : Port3_NativeGeometryBody.Ops C) :
    Port3_NativeGeometryBody.Ops C :=
  {SAQ_GeometrySource.install ops with op12 := fibre indexError}

theorem canonical {C : Type} (indexError : C) (ops : Port3_NativeGeometryBody.Ops C) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install indexError ops) :=
  let h := SAQ_GeometrySource.canonical ops
  ⟨h.point,h.line,h.multiply,h.double,h.one,h.subtract⟩

theorem domain {C : Type} (indexError : C) (ops : Port3_NativeGeometryBody.Ops C) :
    Port5Q1_Domain.SessionADomain (install indexError ops) := by
  constructor
  · exact fibre_law indexError
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

theorem multiply {C : Type} (indexError : C) (ops : Port3_NativeGeometryBody.Ops C) :
    (install indexError ops).op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := rfl

theorem one {C : Type} (indexError : C) (ops : Port3_NativeGeometryBody.Ops C) :
    (install indexError ops).op7=ok 1#u32 := rfl

theorem inverse {C : Type} (indexError : C) (ops : Port3_NativeGeometryBody.Ops C) :
    (install indexError ops).op11=Port4C_InverseExecution.inverse_owned := SAQ_Inverse.source_eq_reference

#print axioms fibre_law
#print axioms canonical
#print axioms domain
#print axioms multiply
#print axioms one
#print axioms inverse
end AspisR1.SAQ_Constructor
end
