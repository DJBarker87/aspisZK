import R1Z.PV_Src_RecordRootDictionary
set_option autoImplicit false
namespace R1Z.PV_Src_RecordRootReturned
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput

theorem source (i : Input) :
    @newRecords (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) i =
      ok (PV_Src_RecordReference.returned PV_Src_CanonicalRoots.table i) := by
  rw [PV_Src_RecordRootDictionary.source]
  exact PV_Src_RecordReference.newRecords_eq _ i

#print axioms source
end R1Z.PV_Src_RecordRootReturned
