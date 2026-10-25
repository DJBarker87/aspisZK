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

theorem proof_bytes : compact.PROOF_BYTES = ok 57607#usize := by
  simp only [verifier.SEMANTIC_BYTES, compact.MAX_NODES, compact.FINAL_LEN, compact.HEADER, compact.OFF_SEMANTIC, compact.SEMANTIC_COMPACT_VALUES, compact.LOGICAL_SEMANTIC, compact.COMPACT_SEMANTIC, compact.OFF_Y1, compact.COMPACT_Y1, compact.OFF_INACTIVE, compact.OFF_ROUND0, compact.OFF_FOLDED_ROOT, compact.OFF_ROUND1, compact.OFF_FINAL, compact.OFF_OPENINGS, compact.OPENING, compact.QUERIES, compact.OFF_NODES, compact.FIXED, compact.MAX_PROOF, compact.PROOF_BYTES]
  decide +kernel

#print axioms any_exact
#print axioms proof_bytes
end Op3I_Header
end
