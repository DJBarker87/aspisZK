import Port9OR_BatchLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchTree
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)

/-- Exact native tree parent. Keys are actual op4/op5 returns; no independent
Parsed/q/nodes, successful map or chosen sorted stream is an argument. -/
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
  let (outIdx,outVal,pending) ← Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys
    (n.val+1) idx val 0#usize 0#usize
  match pending with
  | none => liftResult (fail panic)
  | some r => pure (r,outIdx,outVal)

def factored (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    Result (core.result.Result Unit verifier.Error × Indices × Values) := do
  let raw ← (Port9OR_BatchStep.ops base).op4 queries (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) tree
  let keys ← (Port9OR_BatchStep.ops base).op5 raw (Port4B_TreeCuts.count batch)
  let (outIdx,outVal,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    (Port9OR_BatchStep.ops base) D proof root tree idx val hash (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch tree) keys 0#usize 0#usize
  match pending with | none => fail panic | some r => ok (r,outIdx,outVal)

/-- Only the source's guaranteed-success fixed split/wrapping header is
factored; the actual key builder/sort and loop are unchanged. -/
theorem source_factor (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    factored base D hash proof queries root batch tree idx val=
      Port3_NativeBatchBody.verifier.candidate.batch_tree (Port9OR_BatchStep.ops base)
        D proof queries root batch tree idx val hash := by
  unfold factored Port3_NativeBatchBody.verifier.candidate.batch_tree
  by_cases zero : batch=0#usize
  all_goals simp only [Port4B_TreeCuts.lo,Port4B_TreeCuts.count,Port4B_TreeCuts.hi,
    Port4B_TreeCuts.slot,zero,↓reduceIte,Port9OR_BatchStep.ops,Port3_BatchStd.install,lift,bind_tc_ok]
  all_goals rfl

/-- Full source tree correspondence, including malformed/rejected paths and
arbitrary partial digest failures. No parsed/model-selected keys are used. -/
theorem source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    erase E hash (code base D hash proof queries root batch tree idx val)=
      Port3_NativeBatchBody.verifier.candidate.batch_tree (Port9OR_BatchStep.ops base)
        E proof queries root batch tree idx val hash := by
  rw [← source_factor]
  unfold code factored
  simp only [erase_bind,erase_lift,erase_pure]
  have small : (Port4B_TreeCuts.count batch).val<256 := by
    rw [(Port4B_Bounds.count batch).1];split <;> decide
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro raw _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro keys _
  have loopEq := Port9OR_BatchLoop.source base D E hash proof root tree (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch tree) keys small
    ((Port4B_TreeCuts.count batch).val+1) idx val 0#usize 0#usize (by simp)
  rw [loopEq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro result _
  obtain ⟨outIdx,outVal,pending⟩ := result
  cases pending <;> rfl

#print axioms source_factor
#print axioms source
end AspisR1.Port9OR_BatchTree
end
