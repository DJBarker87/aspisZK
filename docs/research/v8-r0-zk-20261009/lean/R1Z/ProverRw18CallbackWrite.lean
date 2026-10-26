import R1Z.ProverRw18CallbackModel
import R1Z.ProverRw18CanonicalBytes
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CallbackWrite
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

def execute (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Array U32 16#usize)
    (lambda : Q) (out : Slice U8) : Result (Slice U8) := do
  let compressed ← ops.op223 tag (Array.to_slice values) lambda
  ProverRw18QuarticWrite.source compressed out

def value (tag : U32) (values : Array U32 16#usize) (lambda : Q) : K :=
  (R0P.compressPoly (ProverRw18CopyArray.tuple tag values)).eval (ProverRw18FullCarrier.value lambda)

theorem bytes (ops : ProverRwFull.ExternalFuns) (extracted : ProverRw18ContextJoin.Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted=
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops))
    (tag : U32) (values : Array U32 16#usize) (lambda : Q) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : ProverRw18FullCarrier.canonical lambda) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,execute ops tag values lambda out=ok result ∧
      result.val=ProverRw18QuarticBytes.bytes
        (ProverRw18FullCarrier.encode (value tag values lambda))++out.val.drop 16 := by
  unfold execute
  rw [ProverRw18CallbackModel.value ops extracted source_law context_identity tag values lambda htag hlambda]
  simp only [bind_tc_ok]
  exact ProverRw18QuarticBytes.exact_write _ out bound

theorem image (ops : ProverRwFull.ExternalFuns) (extracted : ProverRw18ContextJoin.Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted=
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops))
    (tag : U32) (values : Array U32 16#usize) (lambda : Q) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : ProverRw18FullCarrier.canonical lambda) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,execute ops tag values lambda out=ok result ∧
      result.val.map ProverCommitWordBytes47.rawByte=
        List.ofFn (AspisR1.RetainedFieldByteCodec.encodeQM31LE
          (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm (value tag values lambda)))++
            (out.val.drop 16).map ProverCommitWordBytes47.rawByte := by
  obtain ⟨result,hr,hbytes⟩ := bytes ops extracted source_law context_identity
    tag values lambda out htag hlambda bound
  refine ⟨result,hr,?_⟩
  rw [hbytes,List.map_append]
  unfold ProverRw18FullCarrier.encode
  rw [ProverRw18CanonicalBytes.field_image]

#print axioms bytes
#print axioms image
end R1Z.ProverRw18CallbackWrite
