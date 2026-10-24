import Port4B_KeyInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Install
open Aeneas Aeneas.Std Result

/-- Every native batch child is fixed. The owned key/count/verifier adapters
are the explicitly documented P6 local source/control/library lowerings. -/
def leaves : Port3_NativeBatchBody.Ops where
  op0 := Port3_BatchStd.anyDefault
  op1 := Port3_BatchStd.okOr
  op2 := Port4B_Opening.opening
  op3 := Port4B_SlotInstall.nodeSlot
  op4 := Port4B_KeyInstall.build
  op5 := fun keys n => MultiproofSortRef.sort_reference.sort_rows keys 1#usize n
  op6 := Port4B_LeafCode.native
  op7 := Port3_BatchStd.sameLeaf
  op8 := Port3_BatchStd.sameIndex
  op9 := Array.index_usize
  op10 := Port4B_VerifyInstall.verify
  op11 := Port4B_CountInstall.nodeCount
  op12 := ok (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
  op13 := ok 10#usize
  unwrap8 := Port3_BatchStd.unwrap8

theorem installation (base : Port3_NativeBatchBody.Ops) :
    Port3_BatchStd.install (Port4B_VerifyInstall.install (Port4B_KeyInstall.install base))=leaves := rfl

def batch {X : Type} (D : VTop_Stages.aspis_core.digest.Digest32 X) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) (which : Usize) (hash : X) :=
  Port3_BatchStage.batch leaves D proof p root which hash

theorem parent (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 X) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) (which : Usize) (hash : X) :
    Port3_BatchStage.batch (Port4B_VerifyInstall.install (Port4B_KeyInstall.install base))
      D proof p root which hash=batch D proof p root which hash := by
  unfold batch Port3_BatchStage.batch
  rw [installation,show Port3_BatchStd.install leaves=leaves from rfl]

#print axioms installation
#print axioms parent
end AspisR1.Port4B_Install
end
