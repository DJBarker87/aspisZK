import NMX_R2_CloneNative
import NMX_R2_ResultRelation
import NMX_R2_Heterogeneous
set_option autoImplicit false
noncomputable section
namespace NMX_R2_ClonePacket
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier
/-- Full emitted getter packet on every deferred error, under the retained
std clone/allocator interpretation. No SnapshotError or child-result premise. -/
theorem data (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines bytes
  (NMX_R2_ResultRelation.rust
   (r1_pool_adapter.owned.OwnedAccount.data
    (NMX_R2_CloneNative.install base aborts failure) a))
  (RSL.OwnedAccount.data (account a)) := by
 intro env o run
 change o = NMX_R2_ObserveResult.observe id _ at run
 subst o
 rw [NMX_R2_ResultRelation.map_rust]
 exact NMX_R2_CloneNative.data base aborts failure a env
#print axioms data
end NMX_R2_ClonePacket
end
