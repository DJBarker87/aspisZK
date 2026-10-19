import AspisR1CuQuery.Funs

/-! Focused execution of the emitted salted query widths and variant fold
selector. No parser or whole-query success premise is used here. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsQueryConstants
open Aeneas Aeneas.Std Result AspisR1CuQuery

def folds (v : transport.Variant) : Usize :=
  match v with
  | .S1 => 1#usize
  | .S2 | .D => 2#usize

theorem folds_success (v : transport.Variant) :
    transport.Variant.folds v = .ok (folds v) := by
  cases v <;> rfl

theorem initial_size : verifier.INITIAL_QUERY_BYTES = .ok 3360#usize := by
  simp only [verifier.INITIAL_QUERY_BYTES]
  scalar_tac

theorem second_size : verifier.SECOND_QUERY_BYTES = .ok 1504#usize := by
  simp only [verifier.SECOND_QUERY_BYTES]
  scalar_tac

#print axioms folds_success
#print axioms initial_size
#print axioms second_size
end AspisR1.CuSavingsQueryConstants
