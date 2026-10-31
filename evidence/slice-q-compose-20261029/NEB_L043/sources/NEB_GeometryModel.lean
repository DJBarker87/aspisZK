import NEB_GeometryGatherDomains
import Port5Q1_Geometry
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NEB_GeometryIndices.install ops error with op11:=Port4C_InverseExecution.inverse_owned}

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  have p := NEB_GeometryIndices.primitives ops error
  exact ⟨p.point,p.line,p.multiply,p.double,p.one,p.subtract⟩

/-- All inner canonical primitive predicates and the chosen inverse operation
are instantiated. The premise is the SAME adopted model parent success, not
an additional prefix/inverse/collect success premise or a native claim. -/
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
      out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse) :=
  Port5Q1_Geometry.for_range (install ops error) (primitives ops error) rfl rfl rfl
    queries start end1 out nonempty accepted

#print axioms primitives
#print axioms for_range
end NEB_GeometryModel
end
