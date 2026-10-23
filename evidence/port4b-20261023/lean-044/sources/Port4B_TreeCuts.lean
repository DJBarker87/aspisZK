import Port4B_LeafLoop
import Port4B_AcceptedTail

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_TreeCuts
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

def lo (batch : Usize) : Usize := if batch=0#usize then 0#usize else 10#usize
def hi (batch : Usize) : Usize := if batch=0#usize then 10#usize else 22#usize
def count (batch : Usize) : Usize := Usize.wrapping_sub (hi batch) (lo batch)
def slot (batch kind : Usize) : Usize := Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind

/-- Accepted native tree itself supplies both key-builder/sort returns and
the SAME loop success; all physical query/root/batch/scratch inputs remain. -/
theorem keys (leaves : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
    (batch kind : Usize) (idx outIdx : Indices) (val outVal : Values)
    (accepted : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
      D proof queries root batch kind idx val hash=ok (.Ok (),outIdx,outVal)) :
    ∃ raw sorted,
      leaves.op4 queries (lo batch) (count batch) kind=ok raw ∧
      leaves.op5 raw (count batch)=ok sorted ∧
      Port3_NativeBatchBody.verifier.candidate.batch_tree_loop (Port3_BatchStd.install leaves)
        D proof root kind idx val hash (lo batch) (count batch) (slot batch kind) sorted
        0#usize 0#usize=ok (outIdx,outVal,some (.Ok ())) := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree at accepted
  by_cases zero : batch=0#usize
  all_goals
    simp only [Port3_BatchStd.install,zero,↓reduceIte,lift,bind_tc_ok] at accepted
    simp only [lo,hi,count,slot,zero,↓reduceIte]
    obtain ⟨raw,built,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
    obtain ⟨sorted,sortedCall,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
    obtain ⟨⟨afterIdx,afterVal,pending⟩,loopCall,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
    cases pending with
    | none => cases accepted
    | some r =>
      have same := Result.ok.inj accepted
      cases same
      exact ⟨raw,sorted,built,sortedCall,loopCall⟩

/-- At the terminal key position, the emitted body cannot continue. -/
theorem terminal_shape (leaves : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Array U8 32#usize) (kind lo n slot d : Usize)
    (keys : Array U64 16#usize) (idx : Indices) (val : Values)
    (out : ControlFlow Port4B_LeafStep.LoopState Port4B_LeafStep.LoopOut)
    (step : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install leaves) D proof root kind hash lo n slot keys idx val d n=ok out) :
    ∃ returned, out=.done returned := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body at step
  simp only [lt_self_iff_false,if_false] at step
  repeat' first
  | (solve | cases step)
  | uncase_result
  | head_reduce step
  | split at step
  all_goals cases Result.ok.inj step;exact ⟨_,rfl⟩

/-- Terminal success of the same native loop supplies the exact successful
body iteration consumed by Port4B_AcceptedTail.verify_call. -/
theorem terminal (leaves : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Array U8 32#usize) (kind lo n slot d : Usize)
    (keys : Array U64 16#usize) (idx outIdx : Indices) (val outVal : Values)
    (accepted : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop (Port3_BatchStd.install leaves)
      D proof root kind idx val hash lo n slot keys d n=ok (outIdx,outVal,some (.Ok ()))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body (Port3_BatchStd.install leaves)
      D proof root kind hash lo n slot keys idx val d n=ok (.done (outIdx,outVal,some (.Ok ()))) := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop at accepted
  rw [Aeneas.Std.loop.eq_def] at accepted
  dsimp only at accepted
  generalize step : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
    (Port3_BatchStd.install leaves) D proof root kind hash lo n slot keys idx val d n = r at accepted
  cases r with
  | fail e => cases accepted
  | div => cases accepted
  | ok out =>
    obtain ⟨returned,same⟩ := terminal_shape leaves D hash proof root kind lo n slot d keys idx val out step
    subst out
    have eq := Result.ok.inj accepted
    subst returned
    exact step

#print axioms keys
#print axioms terminal_shape
#print axioms terminal
end AspisR1.Port4B_TreeCuts
end
