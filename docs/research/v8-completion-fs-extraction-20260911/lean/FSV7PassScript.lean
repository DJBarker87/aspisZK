import FSV7ParentScript

/-! Chronological one-level two-tree multiproof interpreter. The recursion
queries the current C1 parent and C2 parent BEFORE recursing into the remaining
entries. An exhausted frontier or fuel returns abort with all earlier oracle
effects retained. This is intentionally not the pure verifier's tail-first
evaluation order. The refinement theorem uses the actual final cache view. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7PassScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSV7PrefixBridge FSV7ParentScript
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.RustShapedMinimalMultiproof

def passScript : (fuel : Nat) → List Entry → List Digests →
    Script (List UInt8) Block Result (2*fuel)
  | _, [], frontier => .done ⟨[], frontier, []⟩
  | 0, _ :: _, _ => .abort
  | fuel+1, head :: rest, frontier =>
    if CanPair head rest then
      match rest with
      | [] => .abort
      | next :: tail =>
        bind (parentScript head.position head.digest next.digest) fun parentEntry =>
          map (prepend parentEntry (nodeCalls head.position head.digest next.digest))
            (passScript fuel tail frontier)
    else
      match frontier with
      | [] => .abort
      | sibling :: tail =>
        bind (parentScript head.position head.digest sibling) fun parentEntry =>
          map (prepend parentEntry (nodeCalls head.position head.digest sibling))
            (passScript fuel rest tail)

/-- Exact chronological log of one successful parent+tail step. This helper
does not assume inclusion and does not erase cached duplicate calls. -/
theorem step_log (tape : Tape) (s : Oracle) (position : Nat) (current sibling : Digests)
    {n : Nat} (tail : Script (List UInt8) Block Result n) (result : Result)
    (tailLog : oldLog (run tape tail (compute tape s position current sibling).2).2 =
      oldLog (compute tape s position current sibling).2 ++ result.trace) :
    oldLog (run tape tail (compute tape s position current sibling).2).2 =
      oldLog s ++ (prepend (compute tape s position current sibling).1
        (nodeCalls position current sibling) result).trace := by
  rw [tailLog, compute_log]
  exact List.append_assoc _ _ _

/-- A successfully executed source-shaped pass constructs the old pure pass
under its OWN final hash view, and its exact chronological call suffix. -/
theorem pass_refines (tape : Tape) (fuel : Nat) (entries : List Entry)
    (frontier : List Digests) (s : Oracle) (result : Result)
    (success : (run tape (passScript fuel entries frontier) s).1 = some result) :
    runPass (oldView (run tape (passScript fuel entries frontier) s).2)
      fuel entries frontier = some result ∧
    oldLog (run tape (passScript fuel entries frontier) s).2 = oldLog s ++ result.trace := by
  induction fuel generalizing entries frontier s result with
  | zero =>
    cases entries with
    | nil =>
      simp only [passScript, run, Option.some.injEq] at success
      subst result
      exact ⟨rfl, (List.append_nil _).symm⟩
    | cons head rest => simp only [passScript, run, reduceCtorEq] at success
  | succ fuel ih =>
    cases entries with
    | nil =>
      simp only [passScript, run, Option.some.injEq] at success
      subst result
      exact ⟨rfl, (List.append_nil _).symm⟩
    | cons head rest =>
      by_cases paired : CanPair head rest
      · cases rest with
        | nil => exact False.elim paired
        | cons next tail =>
          simp only [passScript, if_pos paired, run_bind, run_parent, run_map] at success ⊢
          cases h : (run tape (passScript fuel tail frontier)
              (compute tape s head.position head.digest next.digest).2).1 with
          | none => simp only [h, Option.map_none, reduceCtorEq] at success
          | some output =>
            simp only [h, Option.map_some, Option.some.injEq] at success
            subst result
            obtain ⟨pure, calls⟩ := ih tail frontier
              (compute tape s head.position head.digest next.digest).2 output h
            constructor
            · rw [runPass.eq_def]
              simp only [if_pos paired, pure]
              rw [parent_value_after_script tape s head.position head.digest next.digest
                (passScript fuel tail frontier)]
            · exact step_log tape s head.position head.digest next.digest _ output calls
      · cases frontier with
        | nil => simp only [passScript, if_neg paired, run, reduceCtorEq] at success
        | cons sibling tail =>
          simp only [passScript, if_neg paired, run_bind, run_parent, run_map] at success ⊢
          cases h : (run tape (passScript fuel rest tail)
              (compute tape s head.position head.digest sibling).2).1 with
          | none => simp only [h, Option.map_none, reduceCtorEq] at success
          | some output =>
            simp only [h, Option.map_some, Option.some.injEq] at success
            subst result
            obtain ⟨pure, calls⟩ := ih rest tail
              (compute tape s head.position head.digest sibling).2 output h
            constructor
            · rw [runPass.eq_def]
              simp only [if_neg paired, pure]
              rw [parent_value_after_script tape s head.position head.digest sibling
                (passScript fuel rest tail)]
            · exact step_log tape s head.position head.digest sibling _ output calls

/-- This is the concrete pair of prerequisites later authentication uses:
the pure pass and membership of every emitted call, both produced from the
successful script. No callsIncluded field is supplied by the caller. -/
theorem pass_constructs (tape : Tape) (fuel : Nat) (entries : List Entry)
    (frontier : List Digests) (s : Oracle) (result : Result)
    (success : (run tape (passScript fuel entries frontier) s).1 = some result) :
    Pass (oldView (run tape (passScript fuel entries frontier) s).2)
      entries frontier result.entries result.remaining result.trace ∧
    TraceIncludedInLog result.trace (oldLog (run tape (passScript fuel entries frontier) s).2) := by
  obtain ⟨pure, exactLog⟩ := pass_refines tape fuel entries frontier s result success
  refine ⟨pass_sound _ fuel entries frontier result pure, ?_⟩
  intro input member
  rw [exactLog]
  exact List.mem_append.mpr (Or.inr member)

/-- A level never increases width. This symbolic fact justifies one fixed
q22 allowance for every later level, without expanding depth18 executions. -/
theorem pass_width {view : RawHashInput → Digest208}
    {entries output : List Entry} {frontier remaining : List Digests}
    {trace : OrderedRawQueryLog} (accepted : Pass view entries frontier output remaining trace) :
    output.length ≤ entries.length := by
  induction accepted with
  | nil frontier => exact Nat.le_refl 0
  | pair k current sibling tail ih => simp only [List.length_cons] at *; omega
  | single head sibling unpaired tail ih => simp only [List.length_cons] at *; omega

#print pass_refines
#print pass_constructs
#print axioms step_log
#print axioms pass_refines
#print axioms pass_constructs
#print axioms pass_width
end AspisV8Completion.FSV7PassScript
