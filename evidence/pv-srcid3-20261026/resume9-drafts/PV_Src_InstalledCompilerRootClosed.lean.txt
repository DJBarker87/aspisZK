import R1Z.PV_Src_SourceCompilerRootClosed
import R1Z.PV_Src_RecordAssociation
import R1Z.PV_Src_ExternalAssociation
set_option autoImplicit false
namespace R1Z.PV_Src_InstalledCompilerRootClosed
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort PV_Src_NativeInput

theorem source (external : ExternalLinear) (records : Records)
    (external_law : PV_Src_ExternalAssociation.Associated external)
    (records_law : PV_Src_RecordAssociation.Associated external records) (i : Input) :
    @run external records i = @run PV_Src_ExternalReference.dictionary
      (PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table) i := by
  have he := PV_Src_ExternalAssociation.dictionary external external_law
  have hr := PV_Src_RecordAssociation.dictionary external records records_law
  rw [he] at hr
  rw [he,hr]
  exact PV_Src_SourceCompilerRootClosed.source i

#print axioms source
end R1Z.PV_Src_InstalledCompilerRootClosed
