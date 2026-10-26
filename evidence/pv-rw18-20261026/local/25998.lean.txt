import R1Z.ProverRw18CompressionDecode
import R1Z.ProverRw18WriterContext
import R1Z.ProverRw18FieldFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FixtureDecode
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning ProverRw18FixtureSamples
variable [ProverRwFull.ExternalTypes]

theorem transfer (ops : ProverRwFull.ExternalFuns) (out : Slice U8) (length : out.val.length=16) :
    ∃ result : Slice U8,ProverRw18WriterContext.execute ops transfer_tag
      (Array.to_slice transfer_values) transfer_lambda out=ok result ∧
      (AspisR1.RetainedFieldByteCodec.decodeQM31Bytes
        (result.val.map ProverCommitWordBytes47.rawByte)).map
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv=
            some (ProverRw18FieldReference.value transfer_tag transfer_values.val
              (decode ProverRw18FieldFixtures.lambda)) := by
  rw [ProverRw18WriterContext.closed,← ProverRw18FieldFixtures.transfer_lambda]
  apply ProverRw18CompressionDecode.exact_decode
  · change (1124073472 : Nat)<2147483647;omega
  · exact ProverRw18FieldFixtures.lambda_canonical
  · exact length

theorem withdrawal (ops : ProverRwFull.ExternalFuns) (out : Slice U8) (length : out.val.length=16) :
    ∃ result : Slice U8,ProverRw18WriterContext.execute ops withdrawal_tag
      (Array.to_slice withdrawal_values) withdrawal_lambda out=ok result ∧
      (AspisR1.RetainedFieldByteCodec.decodeQM31Bytes
        (result.val.map ProverCommitWordBytes47.rawByte)).map
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv=
            some (ProverRw18FieldReference.value withdrawal_tag withdrawal_values.val
              (decode ProverRw18FieldFixtures.lambda)) := by
  rw [ProverRw18WriterContext.closed,← ProverRw18FieldFixtures.withdrawal_lambda]
  apply ProverRw18CompressionDecode.exact_decode
  · change (1124073472 : Nat)<2147483647;omega
  · exact ProverRw18FieldFixtures.lambda_canonical
  · exact length

#print axioms transfer
#print axioms withdrawal
end R1Z.ProverRw18FixtureDecode
