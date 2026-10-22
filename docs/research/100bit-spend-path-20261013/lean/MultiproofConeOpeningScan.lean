import MultiproofConeSlices

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeOpeningScan
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical MultiproofConeSlices
open OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

private theorem if_ok_conj (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (ok (decide q) : Result Bool) else ok false) = ok (decide (p ∧ q)) := by
  by_cases hp : p <;> simp [hp]

private theorem ok_decide_same (p : Prop) (a b : Decidable p) :
    (ok (@decide p a) : Result Bool) = ok (@decide p b) := by
  exact congrArg (fun d : Decidable p => ok (@decide p d)) (Subsingleton.elim a b)

/-- Exact strict opening predicate. Salts are excluded by the actual ranges. -/
theorem opening_total (bytes : Slice U8) (length : bytes.val.length = 832) :
    MultiproofParserRef.parser_reference.opening_scan bytes =
      ok (decide (openingCanonical (bytesOf bytes.val))) := by
  have hl : Slice.len bytes = 832#usize := UScalar.eq_of_val_eq length
  have h608 : (608#usize).val ≤ bytes.val.length := by change 608 ≤ bytes.val.length; omega
  have h800 : (800#usize).val ≤ bytes.val.length := by change 800 ≤ bytes.val.length; omega
  rw [MultiproofParserRef.parser_reference.opening_scan]
  simp only [hl,if_true,prefix_total bytes 608#usize h608,bind_tc_ok,
    MultiproofConeCanonical.scan_total,decide_eq_true_eq,
    range_total bytes 672#usize 800#usize (by decide) h800,if_ok_conj]
  simp only [bytes_sub,show (0#usize).val = 0 from rfl,
    show (608#usize).val = 608 from rfl,show (672#usize).val = 672 from rfl,
    show (800#usize).val = 800 from rfl,show 800-672=128 from rfl,
    Nat.sub_zero,openingCanonical,slice,List.drop_zero]
  exact ok_decide_same _ _ _

#print axioms if_ok_conj
#print axioms ok_decide_same
#print axioms opening_total
end AspisR1.MultiproofConeOpeningScan
end
