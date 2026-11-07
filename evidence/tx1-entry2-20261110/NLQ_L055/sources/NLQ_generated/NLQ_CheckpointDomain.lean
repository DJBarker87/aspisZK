import NLQ_Stage1Copy
set_option autoImplicit false
noncomputable section
namespace NLQ_CheckpointDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- Caller clause of the exclusive copy, derived INSIDE its successful child
arm from the SAME returned Vec and SAME computed checkpoint snapshot. No
length or selected-success premise may be added to an enclosing row root. -/
theorem same_length (e : Entry) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 (S2W_ReturnedCheckpoint.nativeBytes saved).length=
 (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 2).1)).length := by
 obtain ⟨account,bytes,index,read,size⟩ := AdapterRw.Cuts.stage1_checkpoint_length ops p e.first d saved branch
 have eqc := Result.ok.inj (index.symm.trans (first_index e).2.2)
 subst account
 obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops (e.snapshot 2 1768 1768) bytes read
 change (if (e.buffers (e.handles 2).1).val.length=1768 ∨
   (e.buffers (e.handles 2).1).val.length=1768 then core.result.Result.Ok (e.buffers (e.handles 2).1)
   else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)=
   core.result.Result.Ok copied at stored
 split at stored
 · have same := core.result.Result.Ok.inj stored
   subst copied
   rw [←view] at size
   simpa only [S2W_ReturnedCheckpoint.nativeBytes,List.length_map,alloc.vec.Vec.len,
    Slice.len,alloc.vec.Vec.deref] using congrArg UScalar.val size
 · cases stored
#check @same_length
#print axioms same_length
end NLQ_CheckpointDomain
