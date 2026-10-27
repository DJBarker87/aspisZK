import R1Z.PV_Src_RootHelper
import R1Z.PV_RunJoin_ShippedExternal
set_option autoImplicit false
namespace R1Z.PV_Src_RootShippedExternal
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual root helper at RunJoin's P6 external extraction adapter. The
shipped/external association remains the named RunJoin unstubbed gate. -/
theorem source : @pool_v1.pair_trace.pair_empty_roots PV_RunJoin_ShippedExternal.E_shipped =
    ok PV_Src_CanonicalRoots.table := PV_Src_RootHelper.source

#print axioms source
end R1Z.PV_Src_RootShippedExternal
