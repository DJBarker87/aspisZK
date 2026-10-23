import CheckpointBytes5Effect

/-! Explicit syscall installation and ordered child-composition laws.
These are conditional source/model transports, not a native reification.
No law equating an arbitrary child Code to actual verifierOps is assumed here
or inferred from equal final bytes. The lead must supply that refinement. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2B_ChildEffects
open CheckpointBytes5Effect

/-- Preserve an inner error as a value and do not execute a suffix child. -/
def thenChild {A B Err : Type} (p : Code (core.result.Result A Err))
    (q : A → Code (core.result.Result B Err)) : Code (core.result.Result B Err) := do
  let r ← p
  match r with
  | .Err e => pure (.Err e)
  | .Ok a => q a

/-- Rejected children retain the exact ordered digest prefix, including
queries made before rejection. No success-only replacement log is selected. -/
theorem rejected_prefix {Execution A B Err Hash : Type} (E : Execution)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (child : Execution → Code (core.result.Result A Err))
    (suffix : A → Code (core.result.Result B Err))
    (before after : Log) (err : Err)
    (rejected : run D hash (child E) before = ok (.Err err,after)) :
    run D hash (thenChild (child E) suffix) before = ok (.Err err,after) := by
  unfold thenChild
  rw [run_bind,rejected]
  rfl

/-- Successful children feed exactly their returned value and state/log into
one continuation. No independent successful continuation is quantified. -/
theorem reached_suffix {Execution A B Err Hash : Type} (E : Execution)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (child : Execution → Code (core.result.Result A Err))
    (suffix : A → Code (core.result.Result B Err))
    (before atReturn : Log) (value : A)
    (returned : run D hash (child E) before = ok (.Ok value,atReturn)) :
    run D hash (thenChild (child E) suffix) before = run D hash (suffix value) atReturn := by
  unfold thenChild
  rw [run_bind,returned]
  rfl

/-- Projection of a successful stateful child to the installed value-level
interpretation. This is one-way and does not manufacture its execution log. -/
theorem value_of_effectful_child {Execution A Hash : Type} (E : Execution)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (child : Execution → Code A) (before after : Log) (value : A)
    (returned : run D hash (child E) before = ok (value,after)) :
    erase D hash (child E) = ok value :=
  run_success D hash (child E) before after value returned

#print axioms rejected_prefix
#print axioms reached_suffix
#print axioms value_of_effectful_child
end AspisR1.S2B_ChildEffects
