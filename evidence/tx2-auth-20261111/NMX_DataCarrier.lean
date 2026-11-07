import NMX_ObserveResult
import NMX_LeafInstall
set_option autoImplicit false
noncomputable section
namespace NMX_DataCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_Carrier NMX_ObserveResult
/-- Exact original bytes/error argument. The CLOSED child domain stays
visible; no arbitrary String clone or allocator stop is silently admitted. -/
theorem data (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (errors : ∀ e, a.bytes = .Err e → NGL_CloneDomain.SnapshotError e) :
 observe bytes (r1_pool_adapter.owned.OwnedAccount.data (NMX_LeafInstall.install ops) a) =
 ⟨.ret (RSL.OwnedAccount.data (account a)),[]⟩ := by
 have closed := NHJ_DataPacket.substitute (NMX_LeafInstall.install ops) a errors
 change observe bytes
  (r1_pool_adapter.owned.OwnedAccount.data
    (NGL_CloneDomain.install (NMX_LeafInstall.install ops)) a) = _
 rw [closed]
 cases hb : a.bytes with
 | Ok v => rfl
 | Err e =>
   simp only [NHJ_DataPacket.G,NHJ_DataPacket.childReply,hb]
   rw [NHJ_DataPacket.exact_error e (errors e hb)]
   rfl
#print axioms data
end NMX_DataCarrier
end
