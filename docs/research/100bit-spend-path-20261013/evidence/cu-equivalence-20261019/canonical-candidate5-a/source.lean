import CuSavingsCanonicalDotsSources
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalCandidate5
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsSources

theorem initialization : new_pairing.EbyKDot.new =
    (do let state ← old_pairing.EbyKDot.new;.ok (project state)) := by
  rw [CuSavingsCanonicalDotsInvariant.old_new,CuSavingsCanonicalDotsInvariant.new_new]
  rfl

theorem finalization (state : old_pairing.EbyKDot) :
    new_pairing.EbyKDot.finish (project state)=old_pairing.EbyKDot.finish state := by
  rw [CuSavingsCanonicalDotsFinish.new_public_finish,CuSavingsCanonicalDotsFinish.old_public_finish]
  rfl

variable [Shared] [AspisR1CanonicalSampler.Shared]
/-- Substitution under an arbitrary unchanged computational context; source
state/value origins discharge repeated-input checks and private-counter bounds.
This is a source API theorem, not a claim of a new compiler theorem. -/
theorem unchanged_context {Output : Type}
    (context : Result (core.result.Result Unit Unit × new_pairing.EbyKDot)→Output)
    (state : old_pairing.EbyKDot) (hs : SourceState state)
    (value : I) (hv : SourceValue value) (scalar : field.QM31) :
    context (new_pairing.EbyKDot.push (project state) (inputToDot value) scalar) =
      context (old_pairing.EbyKDot.push state (inputToDot value) scalar >>=
        fun out=>.ok (projectResult out)) := by
  exact congrArg context (source_push_equivalence state hs value hv scalar)

#print axioms initialization
#print axioms finalization
#print axioms unchanged_context
end AspisR1.CuSavingsCanonicalCandidate5
