import R1Z.PV_Src_ExternalAssociation
import R1Z.PV_Src_RecordRootDictionary
set_option autoImplicit false
namespace R1Z.PV_Src_RecordInstalledExternal
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem source (external : ExternalLinear) (h : PV_Src_ExternalAssociation.Associated external) :
    @PV_Src_RecordDynamic.dictionary external = PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table := by
  rw [PV_Src_ExternalAssociation.dictionary external h]
  exact PV_Src_RecordRootDictionary.source

#print axioms source
end R1Z.PV_Src_RecordInstalledExternal
