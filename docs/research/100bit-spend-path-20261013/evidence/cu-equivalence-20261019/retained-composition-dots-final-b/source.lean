import CuSavingsRetainedCompositionDelayedCandidate4
import CuSavingsRetainedCompositionPrefixPrefixKernel
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionDots
open Aeneas Aeneas.Std Result AspisR1RetainedDots
variable [Shared]
abbrev E := field.wide_exact.WideExact

/-- The exact common emitted middle kernel is a single declaration in this
source interpretation. The old canonical reducer, delayed reducer, and final
fixed-prefix kernel share public field carriers and an opaque dot API. -/
theorem kernel_equivalence (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array E 29#usize) :
    prefix_new_dots.four_dots bytes gamma=old_dots.four_dots bytes gamma := by
  rw [CuSavingsRetainedCompositionPrefixPrefixKernel.source_eq bytes h gamma,
    CuSavingsRetainedCompositionDelayedCandidate4.kernel_equivalence]

/-- The actual checked source View.query discharges the prefix bound. No
query-decoder success or malformed-input length premise is supplied. -/
theorem query_context {Output : Type} (view : AspisR1CuQuery.verifier.View)
    (index : Usize) (gamma : Array E 29#usize)
    (after : Slice U8 → (Unit → Result (Array E 4#usize)) → Result Output) :
    (do let bytes ← AspisR1CuQuery.verifier.View.query view index
        after bytes (fun _ => prefix_new_dots.four_dots bytes gamma)) =
      (do let bytes ← AspisR1CuQuery.verifier.View.query view index
          after bytes (fun _ => old_dots.four_dots bytes gamma)) := by
  apply (bind_eq_iff (AspisR1CuQuery.verifier.View.query view index) _ _).mpr
  intro bytes hquery
  apply congrArg (after bytes)
  funext unit
  exact kernel_equivalence bytes (CuSavingsQueryAccess.query_prefix_bound view index bytes hquery) gamma

/-- Function equality supports the actual transaction's repeated query calls
under any identical continuation, including failures and divergence. -/
theorem all_query_callers {Output : Type} (view : AspisR1CuQuery.verifier.View)
    (gamma : Array E 29#usize)
    (context : (Usize → Result (Array E 4#usize)) → Output) :
    context (fun index => do
      let bytes ← AspisR1CuQuery.verifier.View.query view index
      prefix_new_dots.four_dots bytes gamma) =
      context (fun index => do
        let bytes ← AspisR1CuQuery.verifier.View.query view index
        old_dots.four_dots bytes gamma) := by
  apply congrArg context
  funext index
  exact query_context view index gamma (fun _ run => run ())

#print axioms kernel_equivalence
#print axioms query_context
#print axioms all_query_callers
end AspisR1.CuSavingsRetainedCompositionDots
