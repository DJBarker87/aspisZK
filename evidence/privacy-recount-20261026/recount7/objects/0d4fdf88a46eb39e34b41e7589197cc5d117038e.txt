import R1Z.PV_RunJoin_GeneralIdentification16
import R1Z.PV_Src_SourceCompilerRootClosed
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompilerDictionary16
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open PV_RunJoin_ShippedExternal

abbrev shipped := PV_RunJoin_RecordsAdapter16.R_shipped PV_Src_CanonicalRoots.table

theorem dictionary : shipped = @PV_Src_RecordDynamic.dictionary E_shipped := by
  change Records.mk _ = Records.mk _
  congr 1
  funext i out rec chg snap asset
  exact PV_RunJoin_GeneralIdentification16.general i out rec chg snap asset

theorem frozen_dictionary : shipped =
    PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table :=
  dictionary.trans PV_Src_RecordRootDictionary.source

/-- Exact compiler transport, without a success or supplied-payload premise. -/
theorem compiler (i : PV_Src_NativeInput.Input) :
    @PV_Src_NativeInput.run E_shipped shipped i =
    @PV_Src_NativeInput.run E_shipped
      (@PV_Src_RecordDynamic.dictionary E_shipped) i := by
  rw [dictionary]

theorem compiler_frozen (i : PV_Src_NativeInput.Input) :
    @PV_Src_NativeInput.run E_shipped shipped i =
    @PV_Src_NativeInput.run E_shipped
      (PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table) i := by
  rw [frozen_dictionary]

theorem newRecords (i : PV_Src_NativeInput.Input) :
    @PV_Src_NativeInput.newRecords shipped i =
      ok (PV_Src_RecordReference.returned PV_Src_CanonicalRoots.table i) := by
  rw [frozen_dictionary]
  exact PV_Src_RecordReference.newRecords_eq _ i

#print axioms shipped
#print axioms dictionary
#print axioms frozen_dictionary
#print axioms compiler
#print axioms compiler_frozen
#print axioms newRecords
end R1Z.PV_RunJoin_CompilerDictionary16
