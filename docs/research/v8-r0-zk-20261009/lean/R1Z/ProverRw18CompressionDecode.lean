import R1Z.ProverRw18CompressionWrite
import R1Z.ProverRw18CodecDecode
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CompressionDecode
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem exact_decode (tag : U32) (values : Slice U32) (lambda : Raw) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) (length : out.val.length=16) :
    ∃ result : Slice U8,ProverRw18CompressionWrite.execute tag values (full lambda) out=ok result ∧
      (AspisR1.RetainedFieldByteCodec.decodeQM31Bytes
        (result.val.map ProverCommitWordBytes47.rawByte)).map
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv=
            some (ProverRw18FieldReference.value tag values.val (decode lambda)) := by
  obtain ⟨result,hr,hbytes⟩ := ProverRw18CompressionWrite.bytes tag values lambda out htag hlambda (by omega)
  refine ⟨result,hr,?_⟩
  rw [hbytes,List.drop_eq_nil_iff.mpr (by omega : out.val.length≤16),List.append_nil]
  exact ProverRw18CodecDecode.field _

#print axioms exact_decode
end R1Z.ProverRw18CompressionDecode
