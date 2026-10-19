import AspisR1CuQuery.Funs
import ExtractedCurrentReducerOps

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
  cases v <;>
    simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
      folds,read_discriminant] <;> scalar_tac

theorem add_eq (x y z : Usize) (h : x.val+y.val=z.val) :
    x+y = .ok z := by
  obtain ⟨out,hr,hv⟩ := ExtractedCurrentReducerOps.tryMk_success
    (x.val+y.val) (by rw [h];exact z.bv.isLt)
  change x+y = .ok out at hr
  exact hr.trans (congrArg Result.ok (UScalar.eq_of_val_eq (hv.trans h)))

theorem mul_eq (x y z : Usize) (h : x.val*y.val=z.val) :
    x*y = .ok z := by
  obtain ⟨out,hr,hv⟩ := ExtractedCurrentReducerOps.tryMk_success
    (x.val*y.val) (by rw [h];exact z.bv.isLt)
  change x*y = .ok out at hr
  exact hr.trans (congrArg Result.ok (UScalar.eq_of_val_eq (hv.trans h)))

theorem initial_size : verifier.INITIAL_QUERY_BYTES = .ok 3360#usize := by
  simp only [verifier.INITIAL_QUERY_BYTES,
    add_eq 480#usize 128#usize 608#usize (by scalar_tac),
    add_eq 608#usize 64#usize 672#usize (by scalar_tac),
    mul_eq 2#usize 6#usize 12#usize (by scalar_tac),
    mul_eq 12#usize 7#usize 84#usize (by scalar_tac),
    mul_eq 84#usize 32#usize 2688#usize (by scalar_tac),
    add_eq 672#usize 2688#usize 3360#usize (by scalar_tac),bind_tc_ok]

theorem second_size : verifier.SECOND_QUERY_BYTES = .ok 1504#usize := by
  simp only [verifier.SECOND_QUERY_BYTES,
    mul_eq 4#usize 32#usize 128#usize (by scalar_tac),
    add_eq 128#usize 32#usize 160#usize (by scalar_tac),
    mul_eq 6#usize 7#usize 42#usize (by scalar_tac),
    mul_eq 42#usize 32#usize 1344#usize (by scalar_tac),
    add_eq 160#usize 1344#usize 1504#usize (by scalar_tac),bind_tc_ok]

#print axioms folds_success
#print axioms add_eq
#print axioms mul_eq
#print axioms initial_size
#print axioms second_size
end AspisR1.CuSavingsQueryConstants
