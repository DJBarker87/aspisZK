import NMB_FirstIndex
import S2W_SnapshotJoin
set_option autoImplicit false
noncomputable section
namespace NMB_CheckpointExtent
open Aeneas Aeneas.Std Result AspisR1
/-- Local success inversion supplies the copy domain internally. This is a
branch lemma; no child-success premise may survive in a row root. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 (x.buffers (x.handles 2).1).val.length=1768 := by
 obtain ⟨ca,bytes,ic,read,_⟩ := AdapterRw.Cuts.stage1_checkpoint_length
  ops p (NMB_ThreeSnapshots.first x) d saved accepted
 have eqc := Result.ok.inj (ic.symm.trans (NMB_FirstIndex.source x).2.2)
 subst ca
 obtain ⟨copied,stored,_⟩ := S2W.SnapshotJoin.data_success ops (x.snapshot 2 1768 1768) bytes read
 change (if (x.buffers (x.handles 2).1).val.length=1768 ∨
  (x.buffers (x.handles 2).1).val.length=1768 then core.result.Result.Ok (x.buffers (x.handles 2).1)
  else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)=
  core.result.Result.Ok copied at stored
 split at stored
 · rename_i size
   exact size.elim id id
 · cases stored
#print source
#print axioms source
end NMB_CheckpointExtent
