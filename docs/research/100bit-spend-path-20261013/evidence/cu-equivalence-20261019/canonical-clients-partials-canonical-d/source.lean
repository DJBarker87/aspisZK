import CuSavingsCanonicalDotClients
import CuSavingsCanonicalDotArray
import CuSavingsCanonicalFieldStreamCanonical
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotPartialsCanonical
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotClientFactors CuSavingsCanonicalFieldStreamLoop
open CuSavingsCanonicalDotClients CuSavingsCanonicalDotArray
open OccupancyRangeTraversal
variable [Shared]

theorem row_canonical (f : Slice U8) (common : Array K 16#usize) (s : Usize)
    (value : E) (h : old_clients.shared_row f common s=.ok (.Ok value)) :
    CuSavingsCanonicalDotsField.WideCanonical value := by
  simp only [old_clients.shared_row,CuSavingsCanonicalDotsInvariant.old_new,bind_tc_ok] at h
  rw [old_shared_row_run] at h
  exact CuSavingsCanonicalFieldStreamCanonical.oldRun_success_canonical
    (rowNext f common s) (rowNext_canonical f common s) _ _ value h

theorem loop_canonical (fuel : Nat) (f : Slice U8) (common : Array K 16#usize)
    (iter : OccupancyRangeTraversal.Range) (partials out : Array E 4#usize)
    (hc : CuSavingsCanonicalDotArray.Canonical partials)
    (he : iter.end.val=4) (hi : iter.start.val≤4) (hf : 4-iter.start.val=fuel)
    (h : old_clients.shared_partials_loop iter f common partials=.ok (.Ok out)) :
    CuSavingsCanonicalDotArray.Canonical out := by
  induction fuel generalizing iter partials with
  | zero =>
    have hn := next_done iter (by omega)
    unfold old_clients.shared_partials_loop at h
    rw [loop] at h
    simp only [old_clients.shared_partials_loop.body,hn,bind_tc_ok,uncurry_apply_pair] at h
    cases Result.ok.inj h
    exact hc
  | succ fuel ih =>
    obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    unfold old_clients.shared_partials_loop at h
    rw [loop] at h
    simp only [old_clients.shared_partials_loop.body,hn,bind_tc_ok,uncurry_apply_pair] at h
    cases hr : old_clients.shared_row f common iter.start with
    | fail error => rw [hr] at h; cases h
    | div => rw [hr] at h; cases h
    | ok result =>
      rw [hr] at h
      cases result with
      | Err error => cases h
      | Ok value =>
        have hv := row_canonical f common iter.start value hr
        have hib : iter.start.val<4 := by omega
        have hu := CuSavingsCanonicalDotArray.update partials iter.start value hib
        simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,hu,uncurry_apply_pair] at h
        exact ih next (partials.set iter.start value)
          (CuSavingsCanonicalDotArray.set_canonical partials iter.start hib value hc hv)
          (by rw [hend];exact he) (by omega) (by omega) h

theorem source_canonical (f : Slice U8) (common : Array K 16#usize)
    (out : Array E 4#usize) (h : old_clients.shared_partials f common=.ok (.Ok out)) :
    CanonicalArray out := by
  apply reads_canonical
  apply loop_canonical 4 f common {start:=0#usize,«end»:=4#usize}
    (Array.repeat 4#usize field.wide_exact.WideExact.ZERO) out CuSavingsCanonicalDotArray.zero
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  exact h

/-- The complete original shared-point partial/high source context. Values
supplied to the optimized high dot are outputs of the actual checked row dots. -/
theorem shared_context_equivalence (f : Slice U8) (common : Array K 16#usize)
    (scalars : Array K 4#usize) :
    (do let rows ← new_clients.shared_partials f common
        match rows with
        | .Err error => .ok (core.result.Result.Err error : Output)
        | .Ok values => new_clients.shared_high values scalars) =
    (do let rows ← old_clients.shared_partials f common
        match rows with
        | .Err error => .ok (core.result.Result.Err error : Output)
        | .Ok values => old_clients.shared_high values scalars) := by
  rw [partials_equivalence]
  apply (bind_eq_iff (old_clients.shared_partials f common) _ _).mpr
  intro rows hr
  cases rows with
  | Err error => rfl
  | Ok values => exact high_equivalence values scalars (source_canonical f common values hr)

/-- Every unchanged enclosing continuation may invoke the high dot for any
of the original factor rows, including both shared-point functional slots. -/
theorem caller_context {R : Type} (f : Slice U8) (common : Array K 16#usize)
    (onError : verifier.Error → Result R)
    (after : Array E 4#usize → (Array K 4#usize → Result Output) → Result R) :
    (do let rows ← new_clients.shared_partials f common
        match rows with
        | .Err error => onError error
        | .Ok values => after values (new_clients.shared_high values)) =
    (do let rows ← old_clients.shared_partials f common
        match rows with
        | .Err error => onError error
        | .Ok values => after values (old_clients.shared_high values)) := by
  rw [partials_equivalence]
  apply (bind_eq_iff (old_clients.shared_partials f common) _ _).mpr
  intro rows hr
  cases rows with
  | Err error => rfl
  | Ok values =>
    have hh : new_clients.shared_high values=old_clients.shared_high values := by
      funext scalars
      exact high_equivalence values scalars (source_canonical f common values hr)
    rw [hh]

#print axioms caller_context
#print axioms row_canonical
#print axioms loop_canonical
#print axioms source_canonical
#print axioms shared_context_equivalence
end AspisR1.CuSavingsCanonicalDotPartialsCanonical
