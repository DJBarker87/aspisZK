import FSV7PrefixBridge
import RustShapedMinimalMultiproof

/-! Chronological two-tree parent producer. Requires the parent's exact
historical import build before promotion. No supplied hash equality, log
inclusion, callback correspondence or cache consistency is a premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7ParentScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSAuthenticationPrefixes FSV7PrefixBridge
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths

def answer208 (answer : Block) : Digest208 := digestOfBytes (truncate208 answer)
def paired (left right : Digest208) : Digests := Fin.cases left (fun _ => right)
def input0 (position : Nat) (current sibling : Digests) : RawHashInput :=
  orderedNodeInput position (current 0) (sibling 0)
def input1 (position : Nat) (current sibling : Digests) : RawHashInput :=
  orderedNodeInput position (current 1) (sibling 1)

def compute (tape : Tape) (s : Oracle) (position : Nat) (current sibling : Digests) : Entry × Oracle :=
  let first := query tape s (decode (input0 position current sibling))
  let second := query tape first.2 (decode (input1 position current sibling))
  (⟨position / 2, paired (answer208 first.1) (answer208 second.1)⟩, second.2)

def parentScript (position : Nat) (current sibling : Digests) : Script (List UInt8) Block Entry 2 :=
  .ask (decode (input0 position current sibling)) (fun first =>
    .ask (decode (input1 position current sibling)) (fun second =>
      .done ⟨position / 2, paired (answer208 first) (answer208 second)⟩))

theorem run_parent (tape : Tape) (s : Oracle) (position : Nat) (current sibling : Digests) :
    run tape (parentScript position current sibling) s =
      (some (compute tape s position current sibling).1, (compute tape s position current sibling).2) := rfl

theorem query_oldLog (tape : Tape) (s : Oracle) (input : RawHashInput) :
    oldLog (query tape s (decode input)).2 = oldLog s ++ [input] := by
  obtain ⟨event, eq, inp, _⟩ := query_log tape s (decode input)
  simp only [oldLog, eq, List.map_append, List.map_cons, List.map_nil, inp, encode_decode]

theorem compute_log (tape : Tape) (s : Oracle) (position : Nat) (current sibling : Digests) :
    oldLog (compute tape s position current sibling).2 =
      oldLog s ++ nodeCalls position current sibling := by
  simp only [compute, query_oldLog, nodeCalls, input0, input1, List.append_assoc]
  rfl

/-- Both stored full answers survive any legal later script, including cached
repeats or an abort. Consequently the already computed parent is EXACTLY the
old functional parent's value under the final recorded view. The final view
is derived, never supplied as a supposedly matching independent hash. -/
theorem parent_value_after_script {A : Type} {q : Nat} (tape : Tape) (s : Oracle)
    (position : Nat) (current sibling : Digests) (later : Script (List UInt8) Block A q) :
    (compute tape s position current sibling).1 =
      parent (oldView (run tape later (compute tape s position current sibling).2).2)
        position current sibling := by
  let first := query tape s (decode (input0 position current sibling))
  let second := query tape first.2 (decode (input1 position current sibling))
  have firstStored : first.2.cache (decode (input0 position current sibling)) = some first.1 :=
    answer_installed tape s _
  have secondStored : second.2.cache (decode (input1 position current sibling)) = some second.1 :=
    answer_installed tape first.2 _
  have firstStill : second.2.cache (decode (input0 position current sibling)) = some first.1 :=
    old_answer_preserved tape first.2 _ _ first.1 firstStored
  have final0 := run_preserves_answer tape later second.2 _ first.1 firstStill
  have final1 := run_preserves_answer tape later second.2 _ second.1 secondStored
  have value0 : oldView (run tape later second.2).2 (input0 position current sibling) = answer208 first.1 := by
    simp only [oldView, totalView208, view208, final0, Option.map_some, Option.getD_some, answer208]
  have value1 : oldView (run tape later second.2).2 (input1 position current sibling) = answer208 second.1 := by
    simp only [oldView, totalView208, view208, final1, Option.map_some, Option.getD_some, answer208]
  change (⟨position / 2, paired (answer208 first.1) (answer208 second.1)⟩ : Entry) =
    parent (oldView (run tape later second.2).2) position current sibling
  congr 1
  funext side
  fin_cases side
  · exact value0.symm
  · exact value1.symm

theorem parent_value (tape : Tape) (s : Oracle) (position : Nat) (current sibling : Digests) :
    (compute tape s position current sibling).1 =
      parent (oldView (compute tape s position current sibling).2) position current sibling :=
  parent_value_after_script tape s position current sibling (Script.done () (n := 0))

theorem parent_calls_in_later_log {A : Type} {q : Nat} (tape : Tape) (s : Oracle)
    (position : Nat) (current sibling : Digests) (later : Script (List UInt8) Block A q) :
    TraceIncludedInLog (nodeCalls position current sibling)
      (oldLog (run tape later (compute tape s position current sibling).2).2) := by
  obtain ⟨tail, ht⟩ := run_extends tape later (compute tape s position current sibling).2
  intro input member
  have parentMember : input ∈ oldLog (compute tape s position current sibling).2 := by
    rw [compute_log]
    exact List.mem_append.mpr (Or.inr member)
  simp only [oldLog, ht, List.map_append]
  exact List.mem_append.mpr (Or.inl parentMember)

#print axioms run_parent
#print axioms compute_log
#print axioms parent_value_after_script
#print axioms parent_calls_in_later_log
end AspisV8Completion.FSV7ParentScript
