import R1Z.PV_Src_CanonicalRoots

/-! The remaining root obligation is the actual pure source equation. This
composes the existing root facts with the returned snapshot theorem at the
same compiler payload; it does not replace the root helper with a constant. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_DynamicPublic
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
variable {K : Type} [Field K] [CharP K 2147483647]

theorem correspondence [ExternalLinear] (i : Input)
    (success : @run _ PV_Src_RecordDynamic.dictionary i = ok (.Ok i.compiled))
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (roots : pair_trace.pair_empty_roots = ok PV_Src_CanonicalRoots.table)
    (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords PV_Src_RecordDynamic.dictionary i = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput i))) := by
  apply PV_Src_PublicParts.dynamic_parts i success frontier
  · intro empty hempty
    exact (PV_Src_CanonicalRoots.source_parts (K := K) roots empty hempty).1
  · intro empty hempty
    exact (PV_Src_CanonicalRoots.source_parts (K := K) roots empty hempty).2
  · exact hr

#print axioms correspondence
end R1Z.PV_Src_DynamicPublic
