import NLQ_Stage1CopyPost
import NLQ_ProofPublicFrame
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1WorldFrame
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry
/-- Full SDK value post of the entire source parent, derived from THIS child
result and the internally established copy domain. Not a root success premise. -/
theorem sdk (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 (NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())).post.snapshots.sdk=
 NLQ_CopyMetadata.post (NLQ_Stage1Ready.initial e).snapshots.sdk 2
  (S2W_ReturnedCheckpoint.nativeBytes saved) := by
 rw [NLQ_Stage1CopyPost.source e ops p d saved branch]
 exact (NLQ_WritebackFrame.source e ops p d saved branch).1
/-- Readonly proof/public data cells retain their entire values. Their
cell-disjointness is obtained from the SAME successful owned child. -/
theorem readonly (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 let before := (NLQ_Stage1Ready.initial e).snapshots.sdk
 let after := (NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())).post.snapshots.sdk
 after.cells (before.accounts 0).data=before.cells (before.accounts 0).data ∧
 after.cells (before.accounts 1).data=before.cells (before.accounts 1).data := by
 dsimp only
 rw [sdk e ops p d saved branch]
 exact NLQ_ProofPublicFrame.source e ops p d saved branch
#print sdk
#print readonly
#print axioms sdk
#print axioms readonly
end NLQ_Stage1WorldFrame
