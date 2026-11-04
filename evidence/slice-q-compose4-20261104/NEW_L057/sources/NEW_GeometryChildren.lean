import NEW_GeometryRawRoot
import NEW_GeometryPoint
import NEW_GeometryPolynomial
set_option autoImplicit false
namespace NEW_GeometryChildren
open Aeneas Aeneas.Std Result AspisR1
open NEW_GeometryRawInterface NEW_GeometryPointPrimitives
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem point (u : Usize) : ops.op15 u =
    (NEB_GeometryPrimitives.install ops).op15 u := by
  have h := congrArg (fun r : Result GP => do
    let p ← r
    ok ({x:=p.x,y:=p.y} : AspisR1Stage2.aspis_core.r0.domain.Point U32))
      (NEW_GeometryPoint.complete u)
  simpa only [resultMap_bind,bind_tc_ok,toP] using h

theorem line (u : Usize) : NEW_GeometryActual.fast_domain.line_node u =
    R17FibrePointLineNodeActual.line_node NEA_FieldProduct.ops R17CurrentM31Semantics.operations u := by
  have h := congrArg (fun r : Result GP => do
    let p ← r
    NEW_GeometryPolynomial.cohort p.x) (NEW_GeometryPoint.complete u)
  have contextual : NEW_GeometryActual.fast_domain.line_node u =
      (do let p ← NEW_GeometryActual.fast_domain.fibre_point u
          NEW_GeometryPolynomial.cohort p.x) := by
    change (do let p ← NEW_GeometryActual.fast_domain.fibre_point u
               NEW_GeometryPolynomial.native p.x) = _
    simp only [NEW_GeometryPolynomial.complete]
  rw [contextual]
  change (do let p ← NEW_GeometryActual.fast_domain.fibre_point u
             NEW_GeometryPolynomial.cohort p.x) =
    (do let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point NEA_FieldProduct.ops u
        NEW_GeometryPolynomial.cohort p.x)
  simpa only [resultMap_bind,bind_tc_ok,toP] using h

theorem index (u : Usize) : NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.new u =
    NEB_GeometryIndices.indexPort NEW_GeometryActual.aspis_core.r0.Error.IndexOutOfRange u := by
  simp only [NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.new,
    NEW_GeometryActual.aspis_core.r0.FIBRE_COUNT,bind_tc_ok,
    NEB_GeometryIndices.indexPort,NEA_Reference.fibre_new_ref]
  split <;> rfl

#print NEA_Reference.fibre_new_ref
#print R17CurrentM31Semantics.operations
#print axioms point
#print axioms line
#print axioms index
end NEW_GeometryChildren
