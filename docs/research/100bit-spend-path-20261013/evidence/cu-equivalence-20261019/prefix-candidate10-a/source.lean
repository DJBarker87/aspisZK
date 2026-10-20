import CuSavingsDotsPrefixKernel
import CuSavingsArrayFromFn
set_option autoImplicit false
namespace AspisR1.CuSavingsPrefixCandidate10
open Aeneas Aeneas.Std Result AspisR1CuDots
variable [Arithmetic]
abbrev E := field.wide_exact.WideExact

/-- Complete source helper with the admitted original std array builder. -/
def sourceOld (bytes : Slice U8) (gamma : Array E 29#usize) : Result (Array E 4#usize) :=
  AspisR1CuArrayGraph.core.array.from_fn 4#usize
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (bytes,gamma)

def sourceNew (bytes : Slice U8) (gamma : Array E 29#usize) : Result (Array E 4#usize) := do
  let fixed ← AspisR1CuPrefix.fixed_prefix bytes
  AspisR1CuArrayGraph.core.array.from_fn 4#usize
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (fixed,gamma)

theorem old_library_admission (bytes : Slice U8) (gamma : Array E 29#usize) :
    sourceOld bytes gamma=old_dots.four_dots bytes gamma :=
  CuSavingsArrayFromFn.source_eq_build 4#usize _ _

theorem new_library_admission (bytes : Slice U8) (h : 608≤bytes.val.length)
    (gamma : Array E 29#usize) : sourceNew bytes gamma=new_dots.four_dots bytes gamma := by
  unfold sourceNew
  rw [CuSavingsPrefix.source_success bytes h]
  simp only [bind_tc_ok]
  rw [CuSavingsArrayFromFn.source_eq_build]
  exact (CuSavingsDotsPrefixKernel.optimized_expansion bytes h gamma).symm

theorem helper_equivalence (bytes : Slice U8) (h : 608≤bytes.val.length)
    (gamma : Array E 29#usize) : sourceNew bytes gamma=sourceOld bytes gamma := by
  rw [new_library_admission bytes h gamma,old_library_admission]
  exact CuSavingsDotsPrefixKernel.source_eq bytes h gamma

/-- The sole caller's checked query supplies the bound; the continuation may
perform early rejection, hashes, trace calls, state mutation and settlement. -/
theorem caller_context {T : Type} (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (gamma : Array E 29#usize)
    (ctx : Slice U8 → (Unit→Result (Array E 4#usize)) → Result T) :
    (do let bytes ← AspisR1CuQuery.verifier.View.query view index
        ctx bytes (fun _=>sourceNew bytes gamma)) =
      (do let bytes ← AspisR1CuQuery.verifier.View.query view index
          ctx bytes (fun _=>sourceOld bytes gamma)) := by
  apply (bind_eq_iff (AspisR1CuQuery.verifier.View.query view index) _ _).mpr
  intro bytes hquery
  apply congrArg (ctx bytes)
  funext unit
  exact helper_equivalence bytes
    (CuSavingsQueryAccess.query_prefix_bound view index bytes hquery) gamma

#print axioms old_library_admission
#print axioms new_library_admission
#print axioms helper_equivalence
#print axioms caller_context
end AspisR1.CuSavingsPrefixCandidate10
