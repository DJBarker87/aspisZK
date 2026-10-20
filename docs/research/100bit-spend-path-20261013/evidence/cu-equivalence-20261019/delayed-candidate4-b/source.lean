import CuSavingsDelayedKernel
import CuSavingsArrayFromFn

/-! Candidate 4 is unconditional in the query bytes and gamma carrier.
Consequently ordinary extensional substitution transfers it through every
unchanged caller, including repeated query calls. The source audit pins the
sole production call in query_with_geometry and the unchanged transaction
contexts. No whole-machine/compiler theorem is claimed here. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedCandidate4
open Aeneas Aeneas.Std Result AspisR1DelayedDots
variable [Shared]
abbrev Kernel := Slice U8 → Array field.wide_exact.WideExact 29#usize →
  Result (Array field.wide_exact.WideExact 4#usize)

theorem kernel_equivalence :
    (new_dots.four_dots : Kernel) = old_dots.four_dots := by
  funext bytes gamma
  exact CuSavingsDelayedKernel.source_equivalence bytes gamma

/-- The sole source call's complete prefix/suffix context, including early
rejections or divergence in either unchanged computation. -/
theorem query_context {Input Output : Type} (before : Result Input)
    (bytes : Input → Slice U8)
    (gamma : Input → Array field.wide_exact.WideExact 29#usize)
    (suffix : Input → Array field.wide_exact.WideExact 4#usize → Result Output) :
    (do let state ← before
        let dots ← new_dots.four_dots (bytes state) (gamma state)
        suffix state dots) =
    (do let state ← before
        let dots ← old_dots.four_dots (bytes state) (gamma state)
        suffix state dots) := by
  rw [kernel_equivalence]

/-- Covers arbitrary repeated-call transaction contexts and observations.
The context is computational data, not a proposition assuming equivalence. -/
theorem all_callers_equivalence {Observation : Sort _} (context : Kernel → Observation) :
    context new_dots.four_dots = context old_dots.four_dots :=
  congrArg context kernel_equivalence

omit [Shared] in
/-- Existing source-extracted from_fn admission used for both array sizes. -/
theorem array_source_admission {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) :
    AspisR1CuArrayGraph.core.array.from_fn N inst state =
      CuSavingsArrayBuilder.build N inst state :=
  CuSavingsArrayFromFn.source_eq_build N inst state

#print axioms kernel_equivalence
#print axioms query_context
#print axioms all_callers_equivalence
#print axioms array_source_admission
end AspisR1.CuSavingsDelayedCandidate4
