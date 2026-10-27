import R1Z.PV_Src_RecordRootDictionary
set_option autoImplicit false
namespace R1Z.PV_Src_SourceCompilerRootClosed
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort PV_Src_NativeInput

theorem source (i : Input) :
    @run PV_Src_ExternalReference.dictionary
      (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) i =
    @run PV_Src_ExternalReference.dictionary
      (PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table) i := by
  rw [PV_Src_RecordRootDictionary.source]

#print axioms source
end R1Z.PV_Src_SourceCompilerRootClosed
