import FSV7LevelsScript

/-! Source-shaped guards, depth18 node execution, both root checks and exact
frontier exhaustion. This is a node suffix, not a wire parser or leaf producer.
All rejection branches are actual Script.abort and retain prior oracle calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7NodeVerifierScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSV7PrefixBridge
open FSV7LevelsScript
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.RustShapedMinimalMultiproof

def nodeVerifierScript (roots : Digests) (entries : List Entry) (left right : List Byte) :
    Script (List UInt8) Block OrderedRawQueryLog (2*22*18) :=
  if Guards 18 entries left right then
    bind (m := 0) (n := 2*22*18)
      (levelsScript 22 18 entries (frontierPairs left right)) fun result =>
      match finish roots result with
      | none => Script.abort (n := 0)
      | some trace => Script.done trace (n := 0)
  else .abort

/-- Success constructs the existing guard/level/root/exhaustion verifier
result under the final shared cache, and inclusion of its entire node trace.
No caller supplies a pure verifier result or an independently chosen view. -/
theorem node_verifier_constructs (tape : Tape) (roots : Digests) (entries : List Entry)
    (left right : List Byte) (s : Oracle) (trace : OrderedRawQueryLog)
    (coherent : FSExposureOrder.LogConsistent s)
    (success : (run tape (nodeVerifierScript roots entries left right) s).1 = some trace) :
    verify (oldView (run tape (nodeVerifierScript roots entries left right) s).2)
      roots 18 entries left right = some trace ∧
    oldLog (run tape (nodeVerifierScript roots entries left right) s).2 = oldLog s ++ trace := by
  unfold nodeVerifierScript at success ⊢
  by_cases guards : Guards 18 entries left right
  · simp only [if_pos guards, run_bind] at success ⊢
    cases levelsRun : (run tape (levelsScript 22 18 entries (frontierPairs left right)) s).1 with
    | none => simp only [levelsRun, reduceCtorEq] at success
    | some result =>
      simp only [levelsRun] at success ⊢
      cases finishRun : finish roots result with
      | none => simp only [finishRun, run, reduceCtorEq] at success
      | some returned =>
        simp only [finishRun, run, Option.some.injEq] at success ⊢
        subst trace
        obtain ⟨levelRelation, exactLog⟩ :=
          levels_refines tape 22 18 entries (frontierPairs left right) s result coherent levelsRun
        have pure := pure_levels_complete levelRelation
        obtain ⟨_, _, traceExact⟩ := finish_sound roots result returned finishRun
        constructor
        · simp only [verify, if_pos guards, pure, finishRun]
        · exact exactLog.trans (congrArg (fun tail => oldLog s ++ tail) traceExact)
  · simp only [if_neg guards, run, reduceCtorEq] at success

#print node_verifier_constructs
#print axioms node_verifier_constructs
end AspisV8Completion.FSV7NodeVerifierScript
