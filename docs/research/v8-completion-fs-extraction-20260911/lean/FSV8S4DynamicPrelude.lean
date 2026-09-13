import FSV8S4VerifierOnlySuffix

/-! UNCOMPILED causal wrapper. This is a composition constructor, NOT the
missing semantic-prelude implementation or a resource theorem for it.
The prelude result is computed after the same adversary body and from the
same oracle. It may depend on prior answers; z is not fixed at experiment start.
The pure Context does not include a separately selected accepted transcript. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV8S4DynamicPrelude
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8S4VerifierOnlySuffix
noncomputable section

structure Context where
  z : Fin 10 → FSV8S4VerifierOnlySuffix.K
  cuts : RootCuts
  digestAfterPoints : B

abbrev SuffixResult (body : List UInt8) :=
  Sigma (fun z : Fin 10 → FSV8S4VerifierOnlySuffix.K => Record body z)

def continuation (body : List UInt8) (ctx : Context) :=
  FSTranscriptScript.map
    (fun result : Except Error (Record body ctx.z) × B =>
      ((match result.1 with
        | .error _ => none
        | .ok record => some (Sigma.mk ctx.z record)),result.2))
    (selectedSuffix ctx.z ctx.cuts body ctx.digestAfterPoints)

/-- The actual prelude must supply this Script. The continuation/result type
cannot pair a record for another z/body with the one produced by this run. -/
def withPrelude {n : Nat} (body : List UInt8)
    (prelude : Script (List UInt8) B (Option Context × B) n) :=
  bind prelude (fun result => match result.1 with
    | none => .done ((none : Option (SuffixResult body)), result.2)
    | some ctx => continuation body ctx)

theorem withPrelude_run {n : Nat} (body : List UInt8)
    (prelude : Script (List UInt8) B (Option Context × B) n)
    (tape : Tape) (oracle : Oracle) :
    run tape (withPrelude body prelude) oracle =
      match (run tape prelude oracle).1 with
      | none => (none,(run tape prelude oracle).2)
      | some result => match result.1 with
        | none => (some ((none : Option (SuffixResult body)), result.2),
            (run tape prelude oracle).2)
        | some ctx => run tape (continuation body ctx) (run tape prelude oracle).2 := by
  unfold withPrelude
  rw [run_bind]
  split
  · simp_all
  · rename_i result hresult
    cases hcontext : result.1
    · simp [hresult, hcontext, FSOracleExecution.run]
    · simp [hresult, hcontext]

/-- Even a rejecting prelude retains its exact oracle state; no fresh-cache
reset is inserted between semantic rounds and the PCS suffix. -/
theorem rejected_prelude_keeps_oracle {n : Nat} (body : List UInt8)
    (prelude : Script (List UInt8) B (Option Context × B) n)
    (tape : Tape) (oracle : Oracle) (digest : B)
    (rejected : (run tape prelude oracle).1 = some (none,digest)) :
    (run tape (withPrelude body prelude) oracle).2 = (run tape prelude oracle).2 := by
  rw [withPrelude_run, rejected]

#print axioms withPrelude_run
#print axioms rejected_prelude_keeps_oracle
end
end AspisV8Completion.FSV8S4DynamicPrelude
