import NLM_SnapshotBridge
import NHJ_DataPacket
import NHJ_LengthPacket
set_option autoImplicit false
noncomputable section
namespace NLM_ReadCalls
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- The actual computed snapshot establishes the CLOSED data callee's
error-clone domain. No success, length or independently selected read is assumed. -/
theorem data_domain (e : Entry) (a lo hi : Nat) :
 ∀ err,(e.snapshot a lo hi).bytes=.Err err → NGL_CloneDomain.SnapshotError err := by
 intro err returned
 unfold Entry.snapshot at returned
 dsimp only at returned
 split at returned
 · cases returned
 · cases returned
   exact Or.inr rfl
/-- Complete source call at the exact snapshot record, all bytes lengths and
both deferred-error classes as admitted by NHJ. Native call-site installation
is still needed before this local fact is a parent row certificate. -/
theorem data (ops : AdapterRw.Ops) (e : Entry) (a lo hi : Nat) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot a lo hi)=
 .ok (NHJ_DataPacket.G (e.snapshot a lo hi) (NHJ_DataPacket.childReply (e.snapshot a lo hi))) :=
 NHJ_DataPacket.substitute ops _ (data_domain e a lo hi)
/-- Snapshot stores length even when bytes has a deferred length error. -/
theorem length (ops : AdapterRw.Ops) (e : Entry) (a lo hi : Nat) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (NGL_CloneDomain.install ops)
  (e.snapshot a lo hi)=.ok (.Ok (Slice.len (e.buffers (e.handles a).1))) := by
 rw [NHJ_LengthPacket.substitute ops _ (by intro err returned; cases returned)]
 rfl
#print data_domain
#print data
#print length
#print axioms data_domain
#print axioms data
#print axioms length
end NLM_ReadCalls
