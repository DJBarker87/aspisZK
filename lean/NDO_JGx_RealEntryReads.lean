import JGx_EntryIndices
import NDO_JGx_ProofAccount
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RealEntryReads
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.proof

theorem proof (ops : AdapterRw.Ops) (entry : Entry) (headerBytes : Array U8 688#usize)
    (same : entry.buffers (entry.handles 0).1=JGx_ProofAccount.value headerBytes) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (entry.snapshot 0 58295 58295)=
      ok (.Ok (JGx_ProofAccount.value headerBytes)) := by
  have length : (entry.buffers (entry.handles 0).1).val.length=58295 := by
    rw [same];exact JGx_ProofAccount.length headerBytes
  rw [JGx_EntryReads.data ops entry 0 58295 58295 (Or.inl length),same]
#print axioms proof

theorem checkpoint (ops : AdapterRw.Ops) (entry : Entry)
    (same : entry.buffers (entry.handles 6).1=JFx_NativeBytes.checkpoint) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (entry.snapshot 6 1768 1768)=
      ok (.Ok JFx_NativeBytes.checkpoint) := by
  have length : (entry.buffers (entry.handles 6).1).val.length=1768 := by
    rw [same]
    unfold JFx_NativeBytes.checkpoint
    exact JFx_NativeBytes.checkpointBytes_length
  rw [JGx_EntryReads.data ops entry 6 1768 1768 (Or.inl length),same]
#print axioms checkpoint
end AspisR1.JGx_RealEntryReads
end
