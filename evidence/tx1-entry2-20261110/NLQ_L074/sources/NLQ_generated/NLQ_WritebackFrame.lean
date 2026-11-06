import NLQ_Stage1Ready
import NLQ_CheckpointDomain
set_option autoImplicit false
noncomputable section
namespace NLQ_WritebackFrame
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open NLF_RefCell NLF_SdkModel
/-- The source writeback's full post-state, including guard Drop and owned
cleanup. Length is derived inside THIS computed successful child arm. -/
theorem source (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 let initial := NLQ_Stage1Ready.initial e
 let sdk := initial.snapshots.sdk
 let post := put sdk (sdk.accounts 2).data {sdk.cells (sdk.accounts 2).data with
  payload:={(sdk.cells (sdk.accounts 2).data).payload with bytes:=S2W_ReturnedCheckpoint.nativeBytes saved}}
 (copyResult initial saved).post.snapshots.sdk=post ∧
 (copyResult initial saved).post.snapshots.owned=[] ∧
 (copyResult initial saved).post.checkpoint=none ∧
 (copyResult initial saved).result=.ok (.Ok ()) := by
 dsimp only
 have h := NLQ_Stage1Copy.copy e (S2W_ReturnedCheckpoint.nativeBytes saved)
  (NLQ_CheckpointDomain.same_length e ops p d saved branch)
 change (NLQ_CopyTrace.G (NLQ_Stage1Ready.initial e).snapshots.sdk 2
  (NLQ_Stage1Ready.initial e).snapshots.next (S2W_ReturnedCheckpoint.nativeBytes saved)).outcome=_ at h
 simp only [copyResult,h]
 exact ⟨rfl,rfl,rfl,rfl⟩
#print source
#print axioms source
end NLQ_WritebackFrame
