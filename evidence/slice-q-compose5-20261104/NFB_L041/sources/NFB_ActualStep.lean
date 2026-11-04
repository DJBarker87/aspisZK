import NFB_RangeTrace
set_option autoImplicit false
noncomputable section
namespace NFB_ActualStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary NFB_GatherTrace
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem continuation (start : Usize) (it it1 : It) (lines flat lines1 flat1 : Vec)
 (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=ok (cont (it1,lines1,flat1))) :
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat=
 ok (cont (it1,lines1,flat1)) := by
 have associated := NFB_GeometryInstall.step start it lines flat
 rw [observed] at associated
 cases h : NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat with
 | fail e => simp [h,resultMap] at associated
 | div => simp [h,resultMap] at associated
 | ok flow =>
  cases flow with
  | done value => simp [h,resultMap,NEW_LoopMap.flowMap] at associated
  | cont state =>
   simp only [h,resultMap,NEW_LoopMap.flowMap,Result.ok.injEq,ControlFlow.cont.injEq] at associated
   cases associated
   rfl

/-- Rejected and divergent terminal cuts are exact partial Results too. -/
theorem failed (start : Usize) (it : It) (lines flat : Vec) (error : Aeneas.Std.Error)
 (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=fail error) :
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat=fail error := by
 have associated := NFB_GeometryInstall.step start it lines flat
 rw [observed] at associated
 cases h : NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat <;>
  simp_all [resultMap]
#print axioms continuation
#print axioms failed
end NFB_ActualStep
end
