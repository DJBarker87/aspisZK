import R1Z.PV_Src_RootHelper
set_option autoImplicit false
namespace R1Z.PV_Src_RootReturned
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem source (roots : BuilderRecordsReference.Roots)
    (h : @pool_v1.pair_trace.pair_empty_roots PV_Src_ExternalReference.dictionary = ok roots) :
    roots = PV_Src_CanonicalRoots.table :=
  Result.ok.inj (h.symm.trans PV_Src_RootHelper.source)

#print axioms source
end R1Z.PV_Src_RootReturned
