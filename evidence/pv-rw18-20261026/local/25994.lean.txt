import R1Z.ProverRw18CopyArray
import R1Z.ProverRw18CompressionWrite
import R1Z.ProverRw18CanonicalBytes
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyArrayBytes
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem image (tag : U32) (values : Array U32 16#usize) (lambda : Raw) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,ProverRw18CompressionWrite.execute tag (Array.to_slice values) (full lambda) out=ok result ∧
      result.val.map ProverCommitWordBytes47.rawByte=
        List.ofFn (AspisR1.RetainedFieldByteCodec.encodeQM31LE
          (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm
            ((R0P.compressPoly (ProverRw18CopyArray.tuple tag values)).eval (decode lambda))))++
              (out.val.drop 16).map ProverCommitWordBytes47.rawByte := by
  unfold ProverRw18CompressionWrite.execute
  rw [ProverRw18CopyArray.closed tag values lambda htag hlambda]
  simp only [bind_tc_ok]
  obtain ⟨result,hr,hbytes⟩ := ProverRw18QuarticBytes.exact_write
    (full (ProverRw18FieldEncode.encode
      ((R0P.compressPoly (ProverRw18CopyArray.tuple tag values)).eval (decode lambda)))) out bound
  refine ⟨result,hr,?_⟩
  rw [hbytes,List.map_append,ProverRw18CanonicalBytes.field_image]

#print axioms image
end R1Z.ProverRw18CopyArrayBytes
