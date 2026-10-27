import R1Z.PV_Src_ExternalAssociation
set_option autoImplicit false
namespace R1Z.PV_Src_RootInstalledExternal
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem source (external : ExternalLinear) (h : PV_Src_ExternalAssociation.Associated external) :
    @pool_v1.pair_trace.pair_empty_roots external = ok PV_Src_CanonicalRoots.table := by
  rw [PV_Src_ExternalAssociation.dictionary external h]
  exact PV_Src_RootHelper.source

#print axioms source
end R1Z.PV_Src_RootInstalledExternal
