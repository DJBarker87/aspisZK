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

theorem proof_bytes : compact.PROOF_BYTES = ok 57607#usize := by rfl

#print axioms any_exact
#print axioms proof_bytes
end Op3I_Header
end
