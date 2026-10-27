import R1Z.PV_Src_RecordRootReturned
set_option autoImplicit false
namespace R1Z.PV_Src_RootDynamicWords
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput

theorem source (i : Input) (checked : PV_Src_RecordReference.Checked i)
    (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) i = ok r) :
    r = PV_Src_RecordReference.returned PV_Src_CanonicalRoots.table i ∧
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) := by
  refine ⟨Result.ok.inj (hr.symm.trans (PV_Src_RecordRootReturned.source i)),?_⟩
  exact @PV_Src_RecordDynamic.words PV_Src_ExternalReference.dictionary i checked r hr

#print axioms source
end R1Z.PV_Src_RootDynamicWords
