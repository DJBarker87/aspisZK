import NEW_GeometryContext
set_option autoImplicit false
noncomputable section
namespace NEW_GeometryComplete
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem step (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body ops start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat := by
  rw [dictionary]
  exact NEW_GeometryContext.step start iter lines flat

theorem complete_loop (iter : core.slice.iter.Iter U32) (start : Usize) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 ops iter start lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 adopted iter start lines flat := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0,step]

theorem adopted_root (queries : Array U32 22#usize) (start finish : Usize) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range ops queries start finish =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range adopted queries start finish := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range,complete_loop]

/-- Universal full Result correspondence with the adopted cohort root.
There is no parent-success, child-output, domain or inner-bridge premise. -/
theorem complete_raw (queries : Array U32 22#usize) (start finish : Usize) :
    resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range adopted queries start finish := by
  exact (NEW_GeometryRawRoot.complete queries start finish).trans (adopted_root queries start finish)

/-- Apply the existing lossless error-name transport to the headline cohort interface. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize) :
    Port3_QueryInstall.result
      (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) =
    Port3_GeometryStage.geometry adopted queries start finish := by
  unfold Port3_GeometryStage.geometry
  rw [complete_raw]

/-- Persistent state is unchanged; the complete successful geometry and every
rejection/failure/divergence are retained in the result component. Physical
allocation/copy observations are a separate native packet. -/
theorem result_state {State : Type} (queries : Array U32 22#usize) (start finish : Usize) (state : State) :
    (Port3_QueryInstall.result (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)),state) =
    (Port3_GeometryStage.geometry adopted queries start finish,state) := by
  rw [complete]

/-- The caller's nonempty successful geometry has exactly the adopted flat
order, canonical nonzero operands, SAME-vector reciprocal cells and all five
collected lanes. Acceptance is the root result being characterized. -/
theorem accepted (queries : Array U32 22#usize) (start finish : Usize)
    (out : AspisR1Stage2.verifier.QueryGeometry) (nonempty : start.val<finish.val)
    (run : Port3_QueryInstall.result
      (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=finish.val-start.val ∧
      flat.val.length=5*(finish.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (finish.val-start.val)).map (Port4C_CollectLoop.record inverse) := by
  rw [complete] at run
  exact NEB_ActualGeometryModel.for_range ops err queries start finish out nonempty run

#print axioms step
#print axioms complete_loop
#print axioms adopted_root
#print axioms complete_raw
#print axioms complete
#print axioms result_state
#print axioms accepted
end NEW_GeometryComplete
end
