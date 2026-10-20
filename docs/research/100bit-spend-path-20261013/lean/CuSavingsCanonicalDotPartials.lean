import AspisR1CanonicalDotPartials.Funs
import CuSavingsCanonicalDotClientInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotPartials
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CanonicalDots
variable [Shared]

/-- The outer source loop is common once the exact lifted row computations
are equal. No termination or successful decoder premise is needed here. -/
theorem outer_body_eq (f : Slice U8) (common : Array field.QM31 16#usize)
    (rows : ∀ s, new_clients.shared_row f common s=old_clients.shared_row f common s)
    (iter : core.ops.range.Range Usize)
    (partials : Array field.wide_exact.WideExact 4#usize) :
    new_clients.shared_partials_loop.body f common iter partials=
      old_clients.shared_partials_loop.body f common iter partials := by
  unfold new_clients.shared_partials_loop.body old_clients.shared_partials_loop.body
  simp only [rows]

theorem outer_loop_eq (f : Slice U8) (common : Array field.QM31 16#usize)
    (rows : ∀ s, new_clients.shared_row f common s=old_clients.shared_row f common s)
    (iter : core.ops.range.Range Usize)
    (partials : Array field.wide_exact.WideExact 4#usize) :
    new_clients.shared_partials_loop iter f common partials=
      old_clients.shared_partials_loop iter f common partials := by
  unfold new_clients.shared_partials_loop old_clients.shared_partials_loop
  congr 1
  funext state
  exact outer_body_eq f common rows state.1 state.2

theorem outer_eq (f : Slice U8) (common : Array field.QM31 16#usize)
    (rows : ∀ s, new_clients.shared_row f common s=old_clients.shared_row f common s) :
    new_clients.shared_partials f common=old_clients.shared_partials f common := by
  unfold new_clients.shared_partials old_clients.shared_partials
  exact outer_loop_eq f common rows _ _

#print axioms outer_body_eq
#print axioms outer_loop_eq
#print axioms outer_eq
end AspisR1.CuSavingsCanonicalDotPartials
