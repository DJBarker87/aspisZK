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
  let (lo,hi) ← liftResult (if batch=0#usize then do
    let i ← ops.op13; ok (0#usize,i)
    else do let i ← ops.op13; ok (i,22#usize))
  let n ← liftResult (lift (Usize.wrapping_sub hi lo))
  let i ← liftResult (lift (Usize.wrapping_mul 3#usize batch))
  let slot ← liftResult (lift (Usize.wrapping_add i tree))
  let raw ← liftResult (ops.op4 queries lo n tree)
  let keys ← liftResult (ops.op5 raw n)
  let (outIdx,outVal,pending) ← Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys
    (n.val+1) idx val 0#usize 0#usize
  match pending with
  | none => liftResult (fail panic)
  | some r => pure (r,outIdx,outVal)

/-- Full source tree correspondence at the actual fixed split=10 leaf.
Both actual counts (10/12) follow before the loop; malformed/rejected paths
and arbitrary native partial digest failures are included. -/
theorem source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    erase E hash (code base D hash proof queries root batch tree idx val)=
      Port3_NativeBatchBody.verifier.candidate.batch_tree (Port9OR_BatchStep.ops base)
        E proof queries root batch tree idx val hash := by
  unfold code Port3_NativeBatchBody.verifier.candidate.batch_tree
  by_cases zero : batch=0#usize
  all_goals
    simp only [Port9OR_BatchStep.ops,Port3_BatchStd.install,zero,↓reduceIte,lift,bind_tc_ok,
      erase_bind,erase_lift,erase_pure,Port9OR_BatchStep.pair_match]
    have small : (Usize.wrapping_sub (if batch=0#usize then 10#usize else 22#usize)
      (if batch=0#usize then 0#usize else 10#usize)).val<256 := by
      have counts := (Port4B_Bounds.count batch).1
      unfold Port4B_TreeCuts.count Port4B_TreeCuts.hi Port4B_TreeCuts.lo at counts
      rw [counts];split <;> decide
    simp only [zero,↓reduceIte] at small
    rw [Port9OR_BatchLoop.source base D E hash _ _ _ _ _ _ _ small _ _ _ _ _ (by simp)]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro result _
    obtain ⟨outIdx,outVal,pending⟩ := result
    cases pending <;> rfl

#print axioms source
end AspisR1.Port9OR_BatchTree
end
