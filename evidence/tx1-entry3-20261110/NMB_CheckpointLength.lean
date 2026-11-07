import NMB_CheckpointExtent
set_option autoImplicit false
noncomputable section
namespace NMB_CheckpointLength
open Aeneas Aeneas.Std Result AspisR1
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 saved.val.length=(x.buffers (x.handles 2).1).val.length := by
 obtain ⟨ca,bytes,ic,read,sameLength⟩ := AdapterRw.Cuts.stage1_checkpoint_length
  ops p (NMB_ThreeSnapshots.first x) d saved accepted
 have eqc := Result.ok.inj (ic.symm.trans (NMB_FirstIndex.source x).2.2)
 subst ca
 obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops (x.snapshot 2 1768 1768) bytes read
 have extent := NMB_CheckpointExtent.source x ops p d saved accepted
 have same : (x.buffers (x.handles 2).1).val=copied.val := by
  have normal := stored
  simp only [NMB_Input.Input.snapshot,if_pos (Or.inl extent)] at normal
  exact congrArg (fun (v : alloc.vec.Vec U8) => v.val) (core.result.Result.Ok.inj normal)
 have raw := congrArg UScalar.val sameLength
 rw [←view] at raw
 change saved.val.length=copied.val.length at raw
 rw [←same] at raw
 exact raw
#print source
#print axioms source
end NMB_CheckpointLength
