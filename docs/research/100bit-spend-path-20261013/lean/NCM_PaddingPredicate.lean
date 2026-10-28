import NCE_PaddingPhysical

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_PaddingPredicate
open Aeneas Aeneas.Std Result

abbrev predicate (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) : core.ops.function.FnMut Unit (Slice U8) Bool :=
  Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
    (Port3_BatchStd.install base) D

/-- The exact installed eight-byte predicate is total and computes the
negation of the byte-zero predicate. No successful final scan is assumed. -/
theorem observation (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (chunk : Slice U8)
    (length : chunk.val.length = 8) :
    (predicate base D).call_mut () chunk = ok (!chunk.val.all (fun b => b == 0#u8),()) := by
  let word : Array U8 8#usize := ⟨chunk.val,length⟩
  have same : word.to_slice = chunk := by apply Subtype.ext;rfl
  change Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut
    (Port3_BatchStd.install base) D () chunk = _
  rw [←same,NBJ_Padding.word_exact base D word]
  have bytes : word.to_slice.val = word.val := rfl
  rw [bytes]
  by_cases zero : core.num.U64.from_le_bytes word = 0#u64
  · have all : word.val.all (fun b => b == 0#u8) = true := by
      apply List.all_eq_true.mpr
      intro b mem
      exact beq_iff_eq.mpr ((NBJ_PaddingBits.zero_iff word).mp zero b mem)
    simp only [zero,bne_self_eq_false,all,Bool.not_true]
  · have all : word.val.all (fun b => b == 0#u8) = false := by
      cases checked : word.val.all (fun b => b == 0#u8) with
      | false => rfl
      | true =>
        exfalso
        apply zero
        apply (NBJ_PaddingBits.zero_iff word).mpr
        intro b mem
        exact beq_iff_eq.mp ((List.all_eq_true.mp checked) b mem)
    have nonzero : (core.num.U64.from_le_bytes word != 0#u64) = true := by simpa using zero
    rw [nonzero,all]
    rfl

#print axioms observation
end AspisR1.NCM_PaddingPredicate
end
