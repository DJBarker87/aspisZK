import NMB_HandleSeparation
import NLQ_CopyMetadata
set_option autoImplicit false
noncomputable section
namespace NMB_ReadonlyFrame
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel
def after (x : NMB_Input.Input) (saved : alloc.vec.Vec U8) :=
 NLQ_CopyMetadata.post x.sdk 2 (S2W_ReturnedCheckpoint.nativeBytes saved)
/-- Full cell equality for proof/public, derived from the SAME successful
child's read extents. No metadata equality on aliased cells is assumed. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 (after x saved).cells (x.sdk.accounts 0).data=x.sdk.cells (x.sdk.accounts 0).data ∧
 (after x saved).cells (x.sdk.accounts 1).data=x.sdk.cells (x.sdk.accounts 1).data := by
 have separate := NMB_HandleSeparation.source x ops p d saved accepted
 constructor
 · apply NLQ_CopyFrame.outside
   exact separate.2.1
 · apply NLQ_CopyFrame.outside
   exact separate.2.2
theorem metadata (x : NMB_Input.Input) (saved : alloc.vec.Vec U8) :
 (after x saved).accounts=x.sdk.accounts := rfl
theorem money_tokens (x : NMB_Input.Input) (saved : alloc.vec.Vec U8) (c : Nat) :
 ((after x saved).cells c).payload.money=(x.sdk.cells c).payload.money ∧
 ((after x saved).cells c).readers=(x.sdk.cells c).readers ∧
 ((after x saved).cells c).writer=(x.sdk.cells c).writer :=
 NLQ_CopyMetadata.cell x.sdk 2 c (S2W_ReturnedCheckpoint.nativeBytes saved)
#print source
#print axioms source
#print axioms metadata
#print axioms money_tokens
end NMB_ReadonlyFrame
