import Port6CK_Semantic
import Port5Q2_ReaderWeightJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Weights
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Semantic (Unwrap current)

theorem reads (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (n : Nat) (start : Usize)
    (room : start.val+16*n≤bytes.val.length) (size : bytes.val.length≤4096) :
    Port5Q2_ReaderWeights.reads (current unwrap) bytes n start =
      Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK bytes n start := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [Port5Q2_ReaderWeights.reads,Port5Q2_ReaderWeights.reads]
    rw [show current unwrap ⟨bytes,start⟩=CheckpointBytes3Reader.readK ⟨bytes,start⟩ from
      Port5Q2_ReaderScalar.current_k unwrap unwrap_ok ⟨bytes,start⟩
        (by change start.val+16≤bytes.val.length; omega) size]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair called
    rcases pair with ⟨value,out⟩
    cases value with
    | Err e => rfl
    | Ok x =>
      obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
        ⟨bytes,start⟩ out x (by change start.val+16≤bytes.val.length; omega) called
      dsimp only at cursor
      dsimp only
      rw [ih out.at (by rw [cursor]; omega)]

/-- Native mutable helper with native raw/scalar reads, at its actual Vec
length. No independently successful retained helper is a premise. -/
theorem accepted (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (start finish : Usize)
    (v out : alloc.vec.Vec aspis_core.field.QM31)
    (room : start.val+16*v.val.length≤bytes.val.length) (size : bytes.val.length≤4096)
    (actual : Port5Q2_ReaderWeights.weights (current unwrap) bytes start v=ok (.Ok (out,finish))) :
    CheckpointBytes4Ops.readWeights bytes start v=ok (.Ok (out,finish)) := by
  rw [Port5Q2_ReaderWeights.exact,reads unwrap unwrap_ok bytes v.val.length start room size,
    ← Port5Q2_ReaderWeights.exact] at actual
  exact Port5Q2_ReaderWeightJoin.accepted bytes start finish v out actual

#print axioms reads
#print axioms accepted
end AspisR1.Port6CK_Weights
end
