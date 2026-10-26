import R1Z.ProverRw18CopyArray
import R1Z.ProverRw18FieldFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FixturePolynomial
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning ProverRw18FixtureSamples
variable [ProverRwFull.ExternalTypes]

theorem transfer (ops : ProverRwFull.ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      transfer_tag (Array.to_slice transfer_values) transfer_lambda=
        ok (full (ProverRw18FieldEncode.encode
          ((R0P.compressPoly (ProverRw18CopyArray.tuple transfer_tag transfer_values)).eval
            (decode ProverRw18FieldFixtures.lambda)))) := by
  rw [← ProverRw18FieldFixtures.transfer_lambda]
  apply ProverRw18CopyArray.context ops
  · change (1124073472 : Nat)<2147483647;omega
  · exact ProverRw18FieldFixtures.lambda_canonical

theorem withdrawal (ops : ProverRwFull.ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      withdrawal_tag (Array.to_slice withdrawal_values) withdrawal_lambda=
        ok (full (ProverRw18FieldEncode.encode
          ((R0P.compressPoly (ProverRw18CopyArray.tuple withdrawal_tag withdrawal_values)).eval
            (decode ProverRw18FieldFixtures.lambda)))) := by
  rw [← ProverRw18FieldFixtures.withdrawal_lambda]
  apply ProverRw18CopyArray.context ops
  · change (1124073472 : Nat)<2147483647;omega
  · exact ProverRw18FieldFixtures.lambda_canonical

#print axioms transfer
#print axioms withdrawal
end R1Z.ProverRw18FixturePolynomial
