import R1Z.PV_Src_MapperBody

/-! Complete-word admission for the new explicit mapper transcription. The
actual deployed Records dictionary is not installed by this candidate result. -/
set_option autoImplicit false
namespace R1Z.PV_Src_MapperWords
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput

abbrev dictionary [ExternalLinear] : Records := ⟨PV_Src_MapperBody.call⟩

theorem dictionary_eq [ExternalLinear] : dictionary = PV_Src_RecordDynamic.dictionary := by
  change Records.mk (@PV_Src_MapperBody.call _) = Records.mk (@PV_Src_RecordDynamic.call _)
  apply congrArg Records.mk
  funext input out rec chg snapshot asset
  exact PV_Src_MapperBody.call_eq input out rec chg snapshot asset

theorem words [ExternalLinear] (i : Input) (checked : PV_Src_RecordReference.Checked i)
    (records : pair_forest_copy_builder.CopyRecords)
    (returned : @newRecords dictionary i = ok records) :
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) := by
  rw [dictionary_eq] at returned
  exact PV_Src_RecordDynamic.words i checked records returned

#print axioms dictionary_eq
#print axioms words
end R1Z.PV_Src_MapperWords
