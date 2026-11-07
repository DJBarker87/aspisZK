import NMB_CheckpointLength
import NLQ_CopyTrace
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1CopyDomain
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 (NLQ_CopyTrace.G x.sdk 2 3 (S2W_ReturnedCheckpoint.nativeBytes saved)).outcome=
 .returned (put x.sdk (x.sdk.accounts 2).data {x.sdk.cells (x.sdk.accounts 2).data with
   payload:={(x.sdk.cells (x.sdk.accounts 2).data).payload with bytes:=S2W_ReturnedCheckpoint.nativeBytes saved}})
 (.ok ()) := by
 rw [NLQ_CopyTrace.erasure]
 apply NLF_CopyStep.success
 · rfl
 · rfl
 · change (S2W_ReturnedCheckpoint.nativeBytes saved).length=
    (S2W_ReturnedCheckpoint.nativeBytes (x.buffers (x.handles 2).1)).length
   simpa only [S2W_ReturnedCheckpoint.nativeBytes,List.length_map] using
     NMB_CheckpointLength.source x ops p d saved accepted
#print source
#print axioms source
end NMB_Stage1CopyDomain
