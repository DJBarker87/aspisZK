import R1Z.PV_RunJoin_SemanticComplete40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticLengthReject40
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- The semantic entry rejects a wrong whole-buffer length before copying the
root or any row; the existing output vector is retained exactly. -/
theorem reject (ops : ExternalFuns) (logical : Slice U8) (out : alloc.vec.Vec U8)
    (length : logical.length≠13831) :
    @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops) logical out=
      .ok (.Err compact.CodecError.Length,out) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  have layout : compact.LOGICAL_SEMANTIC=.ok 13831#usize :=
    ProverRwDictionaryLayoutValues.logical_semantic ops
  have different : Slice.len logical≠13831#usize := by
    intro same
    apply length
    exact congrArg UScalar.val same
  have bad : (Slice.len logical != 13831#usize)=true := by
    simpa only [bne_iff_ne] using different
  simp only [host_compact.compact_semantic,layout,bind_tc_ok,bad,↓reduceIte]
#print axioms reject
end R1Z.PV_RunJoin_SemanticLengthReject40
