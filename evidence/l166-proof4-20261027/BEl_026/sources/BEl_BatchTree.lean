import BEl_BatchLoop
import Port9OR_BatchTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_BatchTree
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)

/-- Reference tree on the exact source key/sort/root/slot operands. The actual
native count, padding and in-place verifier remain in the inherited tail. -/
def code (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    Code (core.result.Result Unit verifier.Error × Indices × Values) := do
  let ops := Port9OR_BatchStep.ops base
  let lo := Port4B_TreeCuts.lo batch
  let n := Port4B_TreeCuts.count batch
  let slot := Port4B_TreeCuts.slot batch tree
  let raw ← liftResult (ops.op4 queries lo n tree)
  let keys ← liftResult (ops.op5 raw n)
  let (outIdx,outVal,pending) ← BEl_BatchLoop.code base D hash proof root tree lo n slot keys
    (n.val+1) idx val 0#usize 0#usize
  match pending with
  | none => liftResult (fail panic)
  | some r => pure (r,outIdx,outVal)

theorem observation {S Hash : Type} (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (base : Port3_NativeBatchBody.Ops) (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    BEl_CodeCongr.Equivalent call
      (code base D hash proof queries root batch tree idx val)
      (Port9OR_BatchTree.code base D hash proof queries root batch tree idx val) := by
  unfold code Port9OR_BatchTree.code
  apply BEl_CodeCongr.bind_tail
  intro raw
  apply BEl_CodeCongr.bind_tail
  intro keys
  apply BEl_CodeCongr.bind_head
  exact BEl_BatchLoop.observation call base D hash proof root tree _ _ _ keys _ idx val _ _

#print axioms observation
end AspisR1.BEl_BatchTree
end
