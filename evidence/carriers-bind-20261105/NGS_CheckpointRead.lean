import NGK_COMBINED_IMPORT
import NGR_HistoryPersist
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGS_CHECKPOINT
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers MultiproofConeCanonical

/-- NGR's full account6 buffer equality passes through the SAME indexed read.
No extra persisted-cut or header equality is assumed. -/
theorem loaded_read (e : Entry) (ops : AdapterRw.Ops)
    (account : AdapterRw.Cuts.Account) (checkpoint : Slice U8) (saved : alloc.vec.Vec U8)
    (indexed : Slice.index_usize (e.second secondSizes) 6#usize = ok account)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops account = ok (.Ok checkpoint))
    (loaded : (e.buffers (e.handles 6).1).val = saved.val) :
    bytesOf checkpoint.val = bytesOf saved.val := by
  have index := Result.ok.inj ((SCE_SecondIndex.checkpoint6 e _).symm.trans indexed)
  rw [←index] at read
  have buffer := (SCE_SnapshotRead.buffer e ops 6 _ _ checkpoint read).1
  exact congrArg bytesOf (buffer.trans loaded)

#print axioms loaded_read
end AspisR1.NGS_CHECKPOINT
end
