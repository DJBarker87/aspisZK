import R1Z.PV_Src_RecordDynamic

set_option autoImplicit false
namespace R1Z.PV_Src_RecordDynamicResult
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput

theorem returned [ExternalLinear] (i : Input) (r : pair_forest_copy_builder.CopyRecords)
    (h : @newRecords PV_Src_RecordDynamic.dictionary i = ok r) :
    ∃ roots, pair_trace.pair_empty_roots = ok roots ∧ r = PV_Src_RecordReference.returned roots i := by
  obtain ⟨roots,hroots,hr⟩ := PV_Src_RecordDynamic.newRecords_factor i r h
  rw [PV_Src_RecordReference.newRecords_eq] at hr
  exact ⟨roots,hroots,(Result.ok.inj hr).symm⟩

#print axioms returned
end R1Z.PV_Src_RecordDynamicResult
