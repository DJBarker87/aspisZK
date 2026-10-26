import R1Z.ProverRw18WriterContext
import R1Z.ProverRw18FieldFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FixtureWrite
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning ProverRw18FixtureSamples
variable [ProverRwFull.ExternalTypes]

theorem transfer (ops : ProverRwFull.ExternalFuns) (out : Slice U8) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,ProverRw18WriterContext.execute ops transfer_tag
      (Array.to_slice transfer_values) transfer_lambda out=ok result ∧
      result.val=ProverRw18QuarticBytes.bytes (ProverRw18CompressionWrite.encoded transfer_tag
        (Array.to_slice transfer_values) ProverRw18FieldFixtures.lambda)++out.val.drop 16 := by
  rw [← ProverRw18FieldFixtures.transfer_lambda]
  apply ProverRw18WriterContext.bytes ops
  · change (1124073472 : Nat)<2147483647;omega
  · exact ProverRw18FieldFixtures.lambda_canonical
  · exact bound

theorem withdrawal (ops : ProverRwFull.ExternalFuns) (out : Slice U8) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,ProverRw18WriterContext.execute ops withdrawal_tag
      (Array.to_slice withdrawal_values) withdrawal_lambda out=ok result ∧
      result.val=ProverRw18QuarticBytes.bytes (ProverRw18CompressionWrite.encoded withdrawal_tag
        (Array.to_slice withdrawal_values) ProverRw18FieldFixtures.lambda)++out.val.drop 16 := by
  rw [← ProverRw18FieldFixtures.withdrawal_lambda]
  apply ProverRw18WriterContext.bytes ops
  · change (1124073472 : Nat)<2147483647;omega
  · exact ProverRw18FieldFixtures.lambda_canonical
  · exact bound

#print axioms transfer
#print axioms withdrawal
end R1Z.ProverRw18FixtureWrite
