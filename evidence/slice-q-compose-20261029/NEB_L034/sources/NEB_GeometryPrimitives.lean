import NEB_LineCalls
import Port5Q1_GeometryCanonical
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryPrimitives
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)

/-- Install actual emitted field/point operations. Unrelated standard-library
and error ports remain those of the root physical interpretation. -/
def install {CoreError : Type} (ops : Ops CoreError) : Ops CoreError :=
  {ops with
    op15 := fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point NEA_FieldProduct.ops f
      ok ⟨p.x,p.y⟩
    op14 := R17FibrePointLineNodeActual.line_node NEA_FieldProduct.ops R17CurrentM31Semantics.operations
    op9 := AspisR1Qm31ArithmeticProbe.field.M31.mul
    op10 := AspisR1Qm31ArithmeticProbe.field.M31.double
    op8 := AspisR1Qm31ArithmeticProbe.field.M31.sub
    op7 := ok 1#u32}

/-- This discharges the inner SessionAPrimitives predicate; it is a theorem,
not a new caller premise or an assumed geometry-success conclusion. -/
theorem primitives {CoreError : Type} (ops : Ops CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro f p run
    change (do let q ← AspisR1QueryGeometryActual.fast_domain.fibre_point NEA_FieldProduct.ops f
               ok ({x:=q.x,y:=q.y} : aspis_core.r0.domain.Point U32))=ok p at run
    obtain ⟨q,point,finalRun⟩ := bind_success _ _ _ run
    have cq := NEB_PointSuccess.canonical f q point
    have same : ({x:=q.x,y:=q.y} : aspis_core.r0.domain.Point U32)=p := Result.ok.inj finalRun
    rw [← same]
    exact cq
  · intro f x run
    exact NEB_LineCalls.successful f x run
  · intro x y z cx cy run
    obtain ⟨w,product,_,cw⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
    have same : w=z := Result.ok.inj (product.symm.trans run)
    exact same ▸ cw
  · intro x y cx run
    obtain ⟨w,add,_,cw⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x x cx cx
    have doubled : AspisR1Qm31ArithmeticProbe.field.M31.double x=ok w := by simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
    have same : w=y := Result.ok.inj (doubled.symm.trans run)
    exact same ▸ cw
  · intro x run
    change ok 1#u32=ok x at run
    cases run
    change (1#u32).val<2147483647
    decide
  · intro x y z cx cy run
    obtain ⟨w,sub,_,cw⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x y cx cy
    have same : w=z := Result.ok.inj (sub.symm.trans run)
    exact same ▸ cw

#print axioms primitives
end NEB_GeometryPrimitives
end
