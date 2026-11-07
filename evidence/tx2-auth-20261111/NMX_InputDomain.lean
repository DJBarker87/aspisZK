import NMX_CallArguments
import NHJ_DataPacket
import NHJ_LengthPacket
set_option autoImplicit false
namespace NMX_InputDomain
open Aeneas Aeneas.Std AdapterRw
/-- An explicit optional narrower domain suggested by the CLOSED snapshot
packets. This is NOT silently substituted for canonical233's Domain=True. -/
def SnapshotAccounts (a : NMX_RowSpec_233.Args) : Prop :=
 ∀ account ∈ a.accounts.val, NGL_StorageCases.Domain account

theorem data (a : NMX_RowSpec_233.Args) (domain : SnapshotAccounts a)
 (account : r1_pool_adapter.owned.OwnedAccount) (member : account ∈ a.accounts.val) :
 ∀ e, account.bytes = .Err e → NGL_CloneDomain.SnapshotError e :=
 NHJ_DataPacket.storage_domain account (domain account member)

theorem length (a : NMX_RowSpec_233.Args) (domain : SnapshotAccounts a)
 (account : r1_pool_adapter.owned.OwnedAccount) (member : account ∈ a.accounts.val) :
 NGL_LengthCarrier.domain account.length := by
 unfold NGL_LengthCarrier.domain
 cases hl : account.length with
 | Ok n => exact Or.inl ⟨n,rfl⟩
 | Err e =>
   have exactError := NHJ_LengthPacket.storage_domain account (domain account member) e hl
   subst e
   exact Or.inr (Or.inl rfl)
#print axioms data
#print axioms length
end NMX_InputDomain
