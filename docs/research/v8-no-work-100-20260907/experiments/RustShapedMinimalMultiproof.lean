import MinimalMultiproofPaths

/-! Total functional model of v7_merkle208.rs verify_two_minimal_subtrees_v7_bytes.
The model checks the source guards, walks adjacent entries, consumes one aligned
frontier pair only on the single branch, runs the requested number of levels,
and checks exact frontier exhaustion, singleton position zero and both roots.
Success CONSTRUCTS Pass/Levels/Accepted; none is an input to verify.

Natural-number positions and immutable lists model the bounded u32/Vec walk.
The fuel for one pass is its input length; pass_complete proves this is enough.
The emitted log records C1 then C2 parent calls in loop order. The hash argument
is one pure raw-input-to-208-bit function. This is not Aeneas, Rust memory/byte
code refinement, a probability theorem, or a transcript-freshness assertion.

Inspected source SHA256:
071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.RustShapedMinimalMultiproof
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths

structure Result where
  entries : List Entry
  remaining : List Digests
  trace : OrderedRawQueryLog

instance canPairDecidable (head : Entry) (rest : List Entry) : Decidable (CanPair head rest) := by
  cases rest <;> unfold CanPair <;> infer_instance

def prepend (head : Entry) (calls : OrderedRawQueryLog) (tail : Result) : Result :=
  ⟨head :: tail.entries, tail.remaining, calls ++ tail.trace⟩

/-- One fuel unit is spent per iteration, consuming two entries on the pair
branch. Fuel is not a source-side rejection condition; completeness below
shows input length always suffices for every successful Pass. -/
def runPass (view : RawHashInput → Digest208) :
    Nat → List Entry → List Digests → Option Result
  | _, [], frontier => some ⟨[], frontier, []⟩
  | 0, _ :: _, _ => none
  | fuel+1, head :: rest, frontier =>
    if CanPair head rest then
      match rest with
      | [] => none
      | next :: tail =>
        match runPass view fuel tail frontier with
        | none => none
        | some result => some (prepend (parent view head.position head.digest next.digest)
            (nodeCalls head.position head.digest next.digest) result)
    else
      match frontier with
      | [] => none
      | sibling :: tail =>
        match runPass view fuel rest tail with
        | none => none
        | some result => some (prepend (parent view head.position head.digest sibling)
            (nodeCalls head.position head.digest sibling) result)

private theorem paired_step (view : RawHashInput → Digest208)
    (head next : Entry) (rest output : List Entry)
    (frontier remaining : List Digests) (trace : OrderedRawQueryLog)
    (paired : CanPair head (next :: rest))
    (tail : Pass view rest frontier output remaining trace) :
    Pass view (head :: next :: rest) frontier
      (parent view head.position head.digest next.digest :: output) remaining
      (nodeCalls head.position head.digest next.digest ++ trace) := by
  obtain ⟨k, first, second⟩ := (canPair_iff head next rest).mp paired
  cases head with
  | mk position digest =>
    cases next with
    | mk nextPosition nextDigest =>
      dsimp only at first second
      subst position
      subst nextPosition
      exact Pass.pair k digest nextDigest tail

theorem pass_sound (view : RawHashInput → Digest208) (fuel : Nat)
    (entries : List Entry) (frontier : List Digests) (result : Result)
    (success : runPass view fuel entries frontier = some result) :
    Pass view entries frontier result.entries result.remaining result.trace := by
  induction fuel generalizing entries frontier result with
  | zero =>
    cases entries with
    | nil =>
      simp only [runPass, Option.some.injEq] at success
      subst result
      exact Pass.nil frontier
    | cons head rest => simp [runPass] at success
  | succ fuel ih =>
    cases entries with
    | nil =>
      simp only [runPass, Option.some.injEq] at success
      subst result
      exact Pass.nil frontier
    | cons head rest =>
      rw [runPass.eq_def] at success
      simp only [Nat.add_one] at success
      by_cases paired : CanPair head rest
      · rw [if_pos paired] at success
        cases rest with
        | nil => exact False.elim paired
        | cons next tail =>
          cases call : runPass view fuel tail frontier with
          | none => simp [call] at success
          | some output =>
            simp only [call, Option.some.injEq] at success
            subst result
            exact paired_step view head next tail output.entries frontier
              output.remaining output.trace paired (ih tail frontier output call)
      · rw [if_neg paired] at success
        cases frontier with
        | nil => simp at success
        | cons sibling tail =>
          cases call : runPass view fuel rest tail with
          | none => simp [call] at success
          | some output =>
            simp only [call, Option.some.injEq] at success
            subst result
            exact Pass.single head sibling paired (ih rest tail output call)

/-- The chosen finite fuel never rejects a successful source pass. -/
theorem pass_complete (view : RawHashInput → Digest208)
    {entries output : List Entry} {frontier remaining : List Digests}
    {trace : OrderedRawQueryLog} (run : Pass view entries frontier output remaining trace)
    (fuel : Nat) (enough : entries.length ≤ fuel) :
    runPass view fuel entries frontier = some ⟨output, remaining, trace⟩ := by
  induction run generalizing fuel with
  | nil frontier => cases fuel <;> rfl
  | @pair k left right rest output frontier remaining trace tail ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at enough; omega
    | succ fuel =>
      have smaller : rest.length ≤ fuel := by
        simp only [List.length_cons] at enough
        omega
      have paired : CanPair ⟨2*k, left⟩ (⟨2*k+1, right⟩ :: rest) :=
        (canPair_iff _ _ _).mpr ⟨k, rfl, rfl⟩
      simp only [runPass, if_pos paired, ih fuel smaller, prepend]
  | @single head sibling rest output frontier remaining trace unpaired tail ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at enough; omega
    | succ fuel =>
      have smaller : rest.length ≤ fuel := by
        simp only [List.length_cons] at enough
        omega
      simp only [runPass, if_neg unpaired, ih fuel smaller, prepend]

def runLevels (view : RawHashInput → Digest208) :
    Nat → List Entry → List Digests → Option Result
  | 0, entries, frontier => some ⟨entries, frontier, []⟩
  | depth+1, entries, frontier =>
    match runPass view entries.length entries frontier with
    | none => none
    | some first =>
      match runLevels view depth first.entries first.remaining with
      | none => none
      | some later => some ⟨later.entries, later.remaining, first.trace ++ later.trace⟩

theorem levels_sound (view : RawHashInput → Digest208) (depth : Nat)
    (entries : List Entry) (frontier : List Digests) (result : Result)
    (success : runLevels view depth entries frontier = some result) :
    Levels view depth entries frontier result.entries result.remaining result.trace := by
  induction depth generalizing entries frontier result with
  | zero =>
    simp only [runLevels, Option.some.injEq] at success
    subst result
    exact Levels.zero entries frontier
  | succ depth ih =>
    rw [runLevels] at success
    cases first : runPass view entries.length entries frontier with
    | none => simp [first] at success
    | some output =>
      simp only [first] at success
      cases later : runLevels view depth output.entries output.remaining with
      | none => simp [later] at success
      | some final =>
        simp only [later, Option.some.injEq] at success
        subst result
        exact Levels.succ (pass_sound view entries.length entries frontier output first)
          (ih output.entries output.remaining final later)

/-- Literal adjacent-window comparison, not a supplied sortedness proof. -/
def adjacentCheck : List Entry → Bool
  | [] => true
  | [_] => true
  | head :: next :: rest => decide (head.position < next.position) && adjacentCheck (next :: rest)

theorem adjacent_sound (entries : List Entry) (checked : adjacentCheck entries = true) :
    entries.Pairwise (fun a b => a.position < b.position) := by
  induction entries with
  | nil => exact List.Pairwise.nil
  | cons head rest ih =>
    cases rest with
    | nil => simp
    | cons next tail =>
      have checks : head.position < next.position ∧ adjacentCheck (next :: tail) = true := by
        simpa only [adjacentCheck, Bool.and_eq_true, decide_eq_true_eq] using checked
      have sorted := ih checks.2
      apply List.pairwise_cons.mpr
      refine ⟨?_, sorted⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact checks.1
      · exact Nat.lt_trans checks.1 ((List.pairwise_cons.mp sorted).1 entry member)

def rangeCheck (depth : Nat) (entries : List Entry) : Bool :=
  match entries.getLast? with
  | none => false
  | some entry => decide (entry.position < 2^depth)

/-- Byte length/alignment guards run before any frontier indexing or hashes.
Both arrays share one 26-byte node cursor; each list item below advances it once. -/
def Guards (depth : Nat) (entries : List Entry) (left right : List Byte) : Prop :=
  entries.isEmpty = false ∧ depth < 32 ∧ left.length % 26 = 0 ∧ right.length % 26 = 0 ∧
    left.length = right.length ∧ adjacentCheck entries = true ∧ rangeCheck depth entries = true

instance guardsDecidable (depth : Nat) (entries : List Entry) (left right : List Byte) :
    Decidable (Guards depth entries left right) := by
  unfold Guards
  infer_instance

def frontierPairs (left right : List Byte) : List Digests :=
  List.ofFn fun node : Fin (left.length / 26) => fun side byte =>
    (if side = 0 then left else right).getD (26*node.val+byte.val) 0

theorem frontier_length (left right : List Byte) :
    (frontierPairs left right).length = left.length / 26 := List.length_ofFn

/-- The totalized getD cannot read beyond either checked source array. -/
theorem frontier_in_bounds (left right : List Byte) (same : left.length = right.length)
    (node : Fin (left.length / 26)) (byte : Fin 26) (side : Fin 2) :
    26*node.val+byte.val < (if side = 0 then left else right).length := by
  have nodeBound := node.isLt
  have byteBound := byte.isLt
  split_ifs <;> omega

def finish (roots : Digests) : Result → Option OrderedRawQueryLog
  | ⟨[entry], [], trace⟩ =>
    if entry.position = 0 ∧ entry.digest 0 = roots 0 ∧ entry.digest 1 = roots 1
    then some trace else none
  | _ => none

private theorem root_entry (entry : Entry) (roots : Digests)
    (checked : entry.position = 0 ∧ entry.digest 0 = roots 0 ∧ entry.digest 1 = roots 1) :
    entry = ⟨0, roots⟩ := by
  cases entry with
  | mk position digest =>
    rcases checked with ⟨positionZero, left, right⟩
    dsimp only at positionZero left right
    subst position
    have same : digest = roots := by
      funext side
      fin_cases side
      · exact left
      · exact right
    rw [same]

theorem finish_sound (roots : Digests) (result : Result) (trace : OrderedRawQueryLog)
    (success : finish roots result = some trace) :
    result.entries = [⟨0, roots⟩] ∧ result.remaining = [] ∧ result.trace = trace := by
  rcases result with ⟨entries, remaining, calls⟩
  cases entries with
  | nil => simp [finish] at success
  | cons entry rest =>
    cases rest with
    | cons next tail => simp [finish] at success
    | nil =>
      cases remaining with
      | cons sibling tail => simp [finish] at success
      | nil =>
        simp only [finish] at success
        split at success
        · rename_i checks
          have entryExact := root_entry entry roots checks
          have callsExact := Option.some.inj success
          exact ⟨congrArg (fun item => [item]) entryExact, rfl, callsExact⟩
        · contradiction

/-- Independent verifier: no Pass, Levels or Accepted proof is an input. -/
def verify (view : RawHashInput → Digest208) (roots : Digests) (depth : Nat)
    (entries : List Entry) (left right : List Byte) : Option OrderedRawQueryLog :=
  if Guards depth entries left right then
    match runLevels view depth entries (frontierPairs left right) with
    | none => none
    | some result => finish roots result
  else none

theorem verify_sound (view : RawHashInput → Digest208) (roots : Digests) (depth : Nat)
    (entries : List Entry) (left right : List Byte) (trace : OrderedRawQueryLog)
    (success : verify view roots depth entries left right = some trace) :
    Guards depth entries left right ∧
      Levels view depth entries (frontierPairs left right) [⟨0, roots⟩] [] trace := by
  unfold verify at success
  split at success
  · rename_i guards
    cases call : runLevels view depth entries (frontierPairs left right) with
    | none => simp [call] at success
    | some result =>
      simp only [call] at success
      obtain ⟨entriesExact, remainingExact, traceExact⟩ := finish_sound roots result trace success
      have run := levels_sound view depth entries (frontierPairs left right) result call
      rw [entriesExact, remainingExact, traceExact] at run
      exact ⟨guards, run⟩
  · contradiction

/-- Selected depth18/q22 endpoint. The caller's deterministic descriptor
sort is the existing sortedEntries function; record ordinal is unchanged.
This theorem does not identify the functional run with compiled Rust bytes. -/
theorem verify_selected_accepted (view : RawHashInput → Digest208) (roots : Digests)
    (query : Fin 22 → Position) (records : Fin 22 → Record)
    (left right : List Byte) (trace : OrderedRawQueryLog)
    (success : verify view roots 18 (sortedEntries view query records) left right = some trace) :
    Accepted view roots query records (frontierPairs left right) trace := by
  obtain ⟨guards, run⟩ := verify_sound view roots 18 (sortedEntries view query records)
    left right trace success
  exact ⟨adjacent_sound _ guards.2.2.2.2.2.1, run⟩

#print axioms pass_sound
#print axioms pass_complete
#print axioms levels_sound
#print axioms adjacent_sound
#print axioms frontier_length
#print axioms frontier_in_bounds
#print axioms finish_sound
#print axioms verify_sound
#print axioms verify_selected_accepted
end AspisV8.RustShapedMinimalMultiproof
