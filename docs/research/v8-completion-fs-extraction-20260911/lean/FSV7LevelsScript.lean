import FSV7PassScript
import FSV7ViewPersistence

/-! Chronological arbitrary-depth two-tree node processing. Every parent is
queried before the next parent, every level before the next level. The fixed
width is only a finite execution allowance; successful output is related to
the existing pure verifier with its own input-length fuel. Short or aborting
paths keep the actual cache and log, with no dummy oracle calls.

The initial LogConsistent invariant has a producer in constructBoth and is
preserved by every legal Script. This module does not assert literal Rust
refinement, construct leaves, identify body roots, or charge probabilities. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7LevelsScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSV7PrefixBridge
open FSV7PassScript FSV7ViewPersistence
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.RustShapedMinimalMultiproof

def join (first later : Result) : Result :=
  ⟨later.entries, later.remaining, first.trace ++ later.trace⟩

def levelsScript (width : Nat) : (depth : Nat) → List Entry → List Digests →
    Script (List UInt8) Block Result (2*width*depth)
  | 0, entries, frontier => .done ⟨entries, frontier, []⟩
  | depth+1, entries, frontier =>
    bind (passScript width entries frontier) fun first =>
      map (join first) (levelsScript width depth first.entries first.remaining)

/-- Exact chronological node log plus construction of the pure Levels
relation. No inclusion or matching-hash-function premise is supplied. -/
theorem levels_refines (tape : Tape) (width depth : Nat)
    (entries : List Entry) (frontier : List Digests) (s : Oracle) (result : Result)
    (coherent : FSExposureOrder.LogConsistent s)
    (success : (run tape (levelsScript width depth entries frontier) s).1 = some result) :
    Levels (oldView (run tape (levelsScript width depth entries frontier) s).2)
      depth entries frontier result.entries result.remaining result.trace ∧
    oldLog (run tape (levelsScript width depth entries frontier) s).2 = oldLog s ++ result.trace := by
  induction depth generalizing entries frontier s result with
  | zero =>
    simp only [levelsScript, run, Option.some.injEq] at success
    subst result
    exact ⟨Levels.zero entries frontier, (List.append_nil _).symm⟩
  | succ depth ih =>
    simp only [levelsScript, run_bind] at success ⊢
    cases firstRun : (run tape (passScript width entries frontier) s).1 with
    | none => simp only [firstRun, reduceCtorEq] at success
    | some first =>
      simp only [firstRun, run_map] at success ⊢
      cases tailRun : (run tape (levelsScript width depth first.entries first.remaining)
          (run tape (passScript width entries frontier) s).2).1 with
      | none => simp only [tailRun, Option.map_none, reduceCtorEq] at success
      | some later =>
        simp only [tailRun, Option.map_some, Option.some.injEq] at success
        subst result
        have afterFirst := FSExposureOrder.run_log_consistent tape
          (passScript width entries frontier) s coherent
        obtain ⟨firstPass, firstCalls⟩ :=
          pass_constructs tape width entries frontier s first firstRun
        have firstPreserved := pass_through_later tape
          (run tape (passScript width entries frontier) s).2
          (levelsScript width depth first.entries first.remaining)
          afterFirst firstPass firstCalls
        obtain ⟨tailLevels, tailLog⟩ := ih first.entries first.remaining
          (run tape (passScript width entries frontier) s).2 later afterFirst tailRun
        obtain ⟨_, firstLog⟩ := pass_refines tape width entries frontier s first firstRun
        constructor
        · exact Levels.succ firstPreserved tailLevels
        · rw [tailLog, firstLog]
          exact List.append_assoc _ _ _

/-- The existing pure evaluator's per-level input-length fuel is complete for
a constructed Levels relation. This symbolic bridge avoids expanding depth18. -/
theorem pure_levels_complete {view : RawHashInput → Digest208} {depth : Nat}
    {entries output : List Entry} {frontier remaining : List Digests}
    {trace : OrderedRawQueryLog}
    (accepted : Levels view depth entries frontier output remaining trace) :
    runLevels view depth entries frontier = some ⟨output, remaining, trace⟩ := by
  induction accepted with
  | zero entries frontier => rfl
  | @succ depth entries middle output frontier afterPass remaining first later pass tail ih =>
    have firstExact := pass_complete view pass entries.length (Nat.le_refl _)
    simp only [runLevels, firstExact, ih]

/-- Each level cannot increase the number of active entries. This is the
width prerequisite for proving the fixed q22 script allowance sufficient;
it is not a new selected-profile rejection condition or a converse theorem
that every successful pure execution is already a successful script run. -/
theorem levels_width {view : RawHashInput → Digest208} {depth : Nat}
    {entries output : List Entry} {frontier remaining : List Digests}
    {trace : OrderedRawQueryLog}
    (accepted : Levels view depth entries frontier output remaining trace) :
    output.length ≤ entries.length := by
  induction accepted with
  | zero entries frontier => exact Nat.le_refl _
  | succ pass tail ih => exact Nat.le_trans ih (pass_width pass)

theorem levels_constructs (tape : Tape) (width depth : Nat)
    (entries : List Entry) (frontier : List Digests) (s : Oracle) (result : Result)
    (coherent : FSExposureOrder.LogConsistent s)
    (success : (run tape (levelsScript width depth entries frontier) s).1 = some result) :
    runLevels (oldView (run tape (levelsScript width depth entries frontier) s).2)
      depth entries frontier = some result ∧
    TraceIncludedInLog result.trace
      (oldLog (run tape (levelsScript width depth entries frontier) s).2) ∧
    result.entries.length ≤ entries.length := by
  obtain ⟨pure, exactLog⟩ := levels_refines tape width depth entries frontier s result coherent success
  refine ⟨pure_levels_complete pure, ?_, levels_width pure⟩
  intro input member
  rw [exactLog]
  exact List.mem_append.mpr (Or.inr member)

#print levels_constructs
#print axioms levels_refines
#print axioms pure_levels_complete
#print axioms levels_width
#print axioms levels_constructs
end AspisV8Completion.FSV7LevelsScript
