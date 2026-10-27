import R1Z.PV_Src_RootParents
import R1Z.PV_Src_RootCertificate
set_option autoImplicit false
namespace R1Z.PV_Src_RootHelper
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem source : @pool_v1.pair_trace.pair_empty_roots PV_Src_ExternalReference.dictionary =
    ok PV_Src_CanonicalRoots.table :=
  @PV_Src_RootCertificate.source_eq PV_Src_ExternalReference.dictionary
    PV_Src_CanonicalRoots.table PV_Src_RootCell00.source PV_Src_RootParents.source

#print axioms source
end R1Z.PV_Src_RootHelper
