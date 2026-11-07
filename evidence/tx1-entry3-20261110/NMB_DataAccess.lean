import NMB_SnapshotPacket
import NLQ_SnapshotData
set_option autoImplicit false
noncomputable section
namespace NMB_DataAccess
open Aeneas Aeneas.Std Result AspisR1
/-- Reuse the existing data inversion on a PURE value view. No native world is
replaced, and no equality of metadata on aliases is introduced. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops) (a lo hi : Nat)
 (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (x.snapshot a lo hi)=.ok (.Ok bytes)) :
 bytes=x.buffers (x.handles a).1 ∧
 (x.buffers (x.handles a).1).val.length=lo ∨ bytes=x.buffers (x.handles a).1 ∧
 (x.buffers (x.handles a).1).val.length=hi := by
 have h := NLQ_SnapshotData.returned (NMB_SnapshotPacket.entryAt x a) ops a lo hi bytes read
 rcases h with ⟨same,low|high⟩
 · exact Or.inl ⟨same,low⟩
 · exact Or.inr ⟨same,high⟩
/-- Single decoder-admitted extent at this exact read occurrence. -/
theorem fixed (x : NMB_Input.Input) (ops : AdapterRw.Ops) (a n : Nat) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (x.snapshot a n n)=.ok (.Ok bytes)) :
 bytes=x.buffers (x.handles a).1 ∧ (x.buffers (x.handles a).1).val.length=n := by
 exact (source x ops a n n bytes read).elim id id
#print source
#print fixed
#print axioms source
#print axioms fixed
end NMB_DataAccess
