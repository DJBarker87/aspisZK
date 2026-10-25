import Op3I_Std
import OraclePortHeader
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace Op3I_Header
open Op3I_Source
abbrev nonzero := verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool

theorem any_exact (xs : List U8) :
    ∃ n, Op3I_Std.anyList nonzero xs () = ok (xs.any (fun x => x != 0#u8), n) := by
  induction xs with
  | nil => exact ⟨0,rfl⟩
  | cons x xs ih =>
    obtain ⟨n,ih⟩ := ih
    by_cases hx : (x != 0#u8) = true
    · exact ⟨1,by simp [Op3I_Std.anyList,nonzero,
        verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool,
        verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut,hx]⟩
    · exact ⟨n+1,by simp [Op3I_Std.anyList,nonzero,
        verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool,
        verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut,hx,ih]⟩

theorem add_eq (a b c : Usize) (hv : a.val+b.val=c.val)
    (hb : a.val+b.val ≤ Usize.max) : a+b = ok c := by
  obtain ⟨v,hv',val⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
  rw [hv']
  congr 1
  apply UScalar.eq_of_val_eq
  exact val.trans hv

theorem mul_eq (a b c : Usize) (hv : a.val*b.val=c.val)
    (hb : a.val*b.val ≤ Usize.max) : a*b = ok c := by
  obtain ⟨v,hv',val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=a) (y:=b) (by scalar_tac))
  rw [hv']
  congr 1
  apply UScalar.eq_of_val_eq
  exact val.trans hv

theorem sub_eq (a b c : Usize) (hv : a.val-b.val=c.val)
    (hb : b.val ≤ a.val) : a-b = ok c := by
  obtain ⟨v,hv',val⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=a) (y:=b) hb)
  rw [hv']
  congr 1
  apply UScalar.eq_of_val_eq
  exact val.1.trans hv

theorem proof_bytes : compact.PROOF_BYTES = ok 57607#usize := by
  simp only [verifier.SEMANTIC_BYTES, compact.MAX_NODES, compact.FINAL_LEN, compact.HEADER, compact.OFF_SEMANTIC, compact.SEMANTIC_COMPACT_VALUES, compact.LOGICAL_SEMANTIC, compact.COMPACT_SEMANTIC, compact.OFF_Y1, compact.COMPACT_Y1, compact.OFF_INACTIVE, compact.OFF_ROUND0, compact.OFF_FOLDED_ROOT, compact.OFF_ROUND1, compact.OFF_FINAL, compact.OFF_OPENINGS, compact.OPENING, compact.QUERIES, compact.OFF_NODES, compact.FIXED, compact.MAX_PROOF, compact.PROOF_BYTES]
  simp only [
    add_eq 146#usize 172#usize 318#usize (by decide) (by scalar_tac),
    mul_eq 2#usize 318#usize 636#usize (by decide) (by scalar_tac),
    add_eq 128#usize 150#usize 278#usize (by decide) (by scalar_tac),
    add_eq 636#usize 278#usize 914#usize (by decide) (by scalar_tac),
    mul_eq 32#usize 914#usize 29248#usize (by decide) (by scalar_tac),
    add_eq 480#usize 128#usize 608#usize (by decide) (by scalar_tac),
    add_eq 608#usize 32#usize 640#usize (by decide) (by scalar_tac),
    add_eq 640#usize 32#usize 672#usize (by decide) (by scalar_tac),
    add_eq 672#usize 128#usize 800#usize (by decide) (by scalar_tac),
    add_eq 800#usize 32#usize 832#usize (by decide) (by scalar_tac),
    mul_eq 22#usize 832#usize 18304#usize (by decide) (by scalar_tac),
    mul_eq 64#usize 32#usize 2048#usize (by decide) (by scalar_tac),
    mul_eq 10#usize 28#usize 280#usize (by decide) (by scalar_tac),
    add_eq 1#usize 280#usize 281#usize (by decide) (by scalar_tac),
    add_eq 87#usize 29#usize 116#usize (by decide) (by scalar_tac),
    add_eq 281#usize 116#usize 397#usize (by decide) (by scalar_tac),
    add_eq 397#usize 29#usize 426#usize (by decide) (by scalar_tac),
    mul_eq 16#usize 426#usize 6816#usize (by decide) (by scalar_tac),
    mul_eq 29#usize 32#usize 928#usize (by decide) (by scalar_tac),
    add_eq 12903#usize 928#usize 13831#usize (by decide) (by scalar_tac),
    sub_eq 13831#usize 6816#usize 7015#usize (by decide) (by scalar_tac),
    add_eq 16#usize 7015#usize 7031#usize (by decide) (by scalar_tac),
    mul_eq 29#usize 16#usize 464#usize (by decide) (by scalar_tac),
    add_eq 7031#usize 464#usize 7495#usize (by decide) (by scalar_tac),
    add_eq 7495#usize 32#usize 7527#usize (by decide) (by scalar_tac),
    add_eq 7527#usize 224#usize 7751#usize (by decide) (by scalar_tac),
    add_eq 7751#usize 32#usize 7783#usize (by decide) (by scalar_tac),
    add_eq 7783#usize 224#usize 8007#usize (by decide) (by scalar_tac),
    add_eq 8007#usize 2048#usize 10055#usize (by decide) (by scalar_tac),
    add_eq 10055#usize 18304#usize 28359#usize (by decide) (by scalar_tac),
    add_eq 28359#usize 29248#usize 57607#usize (by decide) (by scalar_tac),
    bind_tc_ok]

#print axioms any_exact
#print axioms add_eq
#print axioms mul_eq
#print axioms sub_eq
#print axioms proof_bytes
end Op3I_Header
end
