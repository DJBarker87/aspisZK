import NEB_GeometryDictionaryEq
import NEB_GeometryModel
set_option autoImplicit false
noncomputable section
namespace NEB_ActualGeometryModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

/-- The actual R17 point/line dictionary, with the checked index reference and
inverse body already selected in the adopted geometry model. This is a model
installation, not a substitute for the missing frozen native root bridge. -/
def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NEB_GeometryModel.install ops error with
    op15 := fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations f
      ok ⟨p.x,p.y⟩
    op14 := R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations}

theorem same_dictionary {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    install ops error = NEB_GeometryModel.install ops error := by
  have hp : (fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations f
      ok ({x:=p.x,y:=p.y} : aspis_core.r0.domain.Point U32)) =
    (fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point NEA_FieldProduct.ops f
      ok ({x:=p.x,y:=p.y} : aspis_core.r0.domain.Point U32)) := by
    funext f
    rw [NEB_GeometryDictionaryEq.point]
  have hl := funext NEB_GeometryDictionaryEq.line
  unfold install
  rw [hp,hl]
  rfl

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  rw [same_dictionary]
  exact NEB_GeometryModel.primitives ops error

/-- Every non-root canonical primitive premise is discharged for the actual
R17 dictionary. The sole success premise is the same parent model Result. -/
theorem for_range {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<end1.val)
    (accepted : Port3_GeometryStage.geometry
      (Port5Q1_GeometryTerminal.install (install ops error)) queries start end1=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=end1.val-start.val ∧
      flat.val.length=5*(end1.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse) := by
  rw [same_dictionary] at accepted
  exact NEB_GeometryModel.for_range ops error queries start end1 out nonempty accepted

#print axioms same_dictionary
#print axioms primitives
#print axioms for_range
end NEB_ActualGeometryModel
end
