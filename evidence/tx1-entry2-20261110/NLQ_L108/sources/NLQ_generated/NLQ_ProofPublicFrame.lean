import NLQ_CopyMetadata
import NLQ_CheckpointDomain
set_option autoImplicit false
noncomputable section
namespace NLQ_ProofPublicFrame
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- The successful owned-child arm ALREADY passed the readonly/writable
metadata guards on these SAME computed snapshots. It therefore supplies
checkpoint/proof/public disjointness for writeback; no distinctness premise
is added to the parent row root. -/
theorem source (e : Entry) (ops : AdapterRw.Ops) (p : AdapterRw.solana_pubkey.Pubkey)
 (d : Slice U8) (saved : alloc.vec.Vec U8)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 let s := (NLQ_SnapshotFold.final e).sdk
 let after := NLQ_CopyMetadata.post s 2 (S2W_ReturnedCheckpoint.nativeBytes saved)
 after.cells (s.accounts 0).data=s.cells (s.accounts 0).data ∧
 after.cells (s.accounts 1).data=s.cells (s.accounts 1).data := by
 dsimp only
 have disjoint := first_disjoint e ops p d saved branch
 constructor
 · apply NLQ_CopyFrame.outside
   exact disjoint 0 (by decide) (by decide)
 · apply NLQ_CopyFrame.outside
   exact disjoint 1 (by decide) (by decide)
#print source
#print axioms source
end NLQ_ProofPublicFrame
