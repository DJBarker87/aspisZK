import NFB_RowG
import NEW_GeometryComplete
set_option autoImplicit false
noncomputable section
namespace NFB_GeometryInstall
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary

/-- Reinstalling std in the already adopted dictionary changes nothing. -/
theorem standard : Port4C_GeometryStd.install adopted=adopted := by rfl

/-- Every emitted one-step Result uses the SAME iterator and both evolving
vectors; contextual arithmetic substitution has no free child premise. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
 resultMap (NEW_LoopMap.flowMap answer)
   (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start iter lines flat)=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat :=
 (NEW_GeometryRawBody.step start iter lines flat).trans
   (NEW_GeometryComplete.step start iter lines flat)

/-- Whole partial Result, including all rejection/failure/divergence branches.
The native physical packet is separately checked by the hybrid validator. -/
theorem loop (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
 resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0 iter start lines flat)=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 adopted iter start lines flat :=
 (NEW_GeometryRawRoot.complete_loop start iter lines flat).trans
   (NEW_GeometryComplete.complete_loop iter start lines flat)

#print axioms standard
#print axioms step
#print axioms loop
end NFB_GeometryInstall
end
