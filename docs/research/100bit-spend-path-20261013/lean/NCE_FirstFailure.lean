import NBY_Audit
import MultiproofConeP6Frozen2Stage
import Port4B_BatchJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_FirstFailure
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Slot := Nat → Nat → reference.Scratch → Program Bytes State (Bool × reference.Scratch)
abbrev Log := List (Bytes × State)

/-- An observation of the EXISTING slot execution, with the first failed tree
retained. This adds no native interpreter or independently selected execution.
Each next call uses exactly the preceding call's returned scratch. -/
def observe (H : Bytes → State) (slot : Slot) :
    List (Nat × Nat) → reference.Scratch → Log × Option (Nat × Nat) × reference.Scratch
  | [],s => ([],none,s)
  | (b,k)::rest,s =>
      let out := eval H (slot b k s)
      if out.2.1 then
        let tail := observe H slot rest out.2.2
        (out.1++tail.1,tail.2.1,tail.2.2)
      else (out.1,some (b,k),out.2.2)

/-- Full log and final scratch agree with the existing cohort sequence on
both success and rejection, including the rejecting child's own digest log. -/
theorem sequence_observation (H : Bytes → State) (slot : Slot)
    (ss : List (Nat × Nat)) (s : reference.Scratch) :
    eval H (MultiproofConeP6Frozen2Stage.sequence slot ss s) =
      let out := observe H slot ss s
      (out.1,(out.2.1.isNone,out.2.2)) := by
  induction ss generalizing s with
  | nil => rfl
  | cons bk rest ih =>
    rcases bk with ⟨b,k⟩
    simp only [MultiproofConeP6Frozen2Stage.sequence,eval_bind,observe]
    cases h : eval H (slot b k s) with
    | mk log returned =>
      rcases returned with ⟨accepted,after⟩
      cases accepted with
      | false => simp only [Bool.false_eq_true,if_false,eval,List.append_nil]; rfl
      | true => simp only [if_true,ih]

/-- An already-issued prefix remains before ALL tree reads. Rejection does
not erase it and no digest after the first failed tree is evaluated. -/
theorem prefix_observation (H : Bytes → State) (slot : Slot)
    (ss : List (Nat × Nat)) (s : reference.Scratch) (before : Log) :
    let out := observe H slot ss s
    (before ++ (eval H (MultiproofConeP6Frozen2Stage.sequence slot ss s)).1,
      (eval H (MultiproofConeP6Frozen2Stage.sequence slot ss s)).2) =
      (before++out.1,(out.2.1.isNone,out.2.2)) := by
  rw [sequence_observation]

/-- A local false return stops at this child, retaining exactly its full log
and returned scratch. The unvisited suffix is arbitrary. -/
theorem stop_here (H : Bytes → State) (slot : Slot) (b k : Nat)
    (rest : List (Nat × Nat)) (s after : reference.Scratch) (log : Log)
    (returned : eval H (slot b k s) = (log,(false,after))) :
    observe H slot ((b,k)::rest) s = (log,some (b,k),after) := by
  simp only [observe,returned,Bool.false_eq_true,if_false]

/-- Successful dispatch carries the actual poststate and log into the next
child. This is a model control lemma, NOT a native whole-child premise. -/
theorem continue_here (H : Bytes → State) (slot : Slot) (b k : Nat)
    (rest : List (Nat × Nat)) (s after : reference.Scratch) (log : Log)
    (returned : eval H (slot b k s) = (log,(true,after))) :
    observe H slot ((b,k)::rest) s =
      let tail := observe H slot rest after
      (log++tail.1,tail.2.1,tail.2.2) := by
  simp only [observe,returned,if_true]

/-- The existing P6 batch, with no acceptance premise, is exactly the
first-failure observation of its own three chronological tree executions.
This does NOT instantiate any of the eight missing Rust/native cuts. -/
theorem batch_observation (H : Bytes → State)
    (occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf) (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (b : Nat) (s : reference.Scratch) :
    eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf p q nodes b s) =
      let out := observe H (fun b k s => MultiproofConeP6Batch.batch_tree
        (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf p q b k (nodes b k) s)
        [(b,0),(b,1),(b,2)] s
      (out.1,out.2.1.isNone) := by
  simp only [MultiproofConeP6Frozen2Stage.sourceBatch,eval_bind,sequence_observation,
    eval,List.append_nil]

#print axioms sequence_observation
#print axioms prefix_observation
#print axioms stop_here
#print axioms continue_here
#print axioms batch_observation
end AspisR1.NCE_FirstFailure
end
