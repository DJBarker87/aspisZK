import AspisR1TerminalDecoder.Funs
import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PublicDigest29
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem canon_lanes (d : Array U32 8#usize) : Canon8 d ↔
    d.val[0]!.val < 2147483647 ∧ d.val[1]!.val < 2147483647 ∧
    d.val[2]!.val < 2147483647 ∧ d.val[3]!.val < 2147483647 ∧
    d.val[4]!.val < 2147483647 ∧ d.val[5]!.val < 2147483647 ∧
    d.val[6]!.val < 2147483647 ∧ d.val[7]!.val < 2147483647 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
      h 4 (by decide),h 5 (by decide),h 6 (by decide),h 7 (by decide)⟩
  · intro h j hj
    interval_cases j <;> tauto
#print axioms canon_lanes

/-- Exact canonical-digest test used by both public statement validators. -/
theorem canonical_iff (d : Array U32 8#usize) :
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical d = ok true ↔ Canon8 d := by
  rw [canon_lanes]
  unfold AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical
  simp only [index_ok_gen d 0#usize (by decide),index_ok_gen d 1#usize (by decide),
    index_ok_gen d 2#usize (by decide),index_ok_gen d 3#usize (by decide),
    index_ok_gen d 4#usize (by decide),index_ok_gen d 5#usize (by decide),
    index_ok_gen d 6#usize (by decide),index_ok_gen d 7#usize (by decide),bind_tc_ok]
  simp only [AspisR1TerminalDecoder.aspis_core.field.P,UScalar.lt_equiv,UScalar.ofNatCore_val_eq]
  split_ifs <;> simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true,
    false_iff,true_and,false_and,and_false,and_true,not_false_eq_true]
#print axioms canonical_iff
end R1Z.PV_RunJoin_PublicDigest29
