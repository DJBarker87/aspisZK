import R1Z.ProverRw18FieldReference
import R1Z.ProverRw18FixtureSamples
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldFixtures
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

def lambda : Raw := ⟨⟨7#u32,11#u32⟩,⟨17#u32,19#u32⟩⟩

theorem lambda_canonical : Canonical lambda := by
  change ((7 : Nat)<2147483647 ∧ 11<2147483647) ∧
    (17<2147483647 ∧ 19<2147483647)
  omega

theorem transfer_lambda : full lambda=ProverRw18FixtureSamples.transfer_lambda := rfl

theorem withdrawal_lambda : full lambda=ProverRw18FixtureSamples.withdrawal_lambda := rfl

variable [ProverRwFull.ExternalTypes]

theorem transfer (ops : ProverRwFull.ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      ProverRw18FixtureSamples.transfer_tag
      (Array.to_slice ProverRw18FixtureSamples.transfer_values)
      ProverRw18FixtureSamples.transfer_lambda =
        ProverRw18FieldReference.reference ProverRw18FixtureSamples.transfer_tag
          (Array.to_slice ProverRw18FixtureSamples.transfer_values) lambda := by
  rw [← transfer_lambda]
  apply ProverRw18FieldReference.context ops
  · change (1124073472 : Nat)<2147483647
    omega
  · exact lambda_canonical

theorem withdrawal (ops : ProverRwFull.ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      ProverRw18FixtureSamples.withdrawal_tag
      (Array.to_slice ProverRw18FixtureSamples.withdrawal_values)
      ProverRw18FixtureSamples.withdrawal_lambda =
        ProverRw18FieldReference.reference ProverRw18FixtureSamples.withdrawal_tag
          (Array.to_slice ProverRw18FixtureSamples.withdrawal_values) lambda := by
  rw [← withdrawal_lambda]
  apply ProverRw18FieldReference.context ops
  · change (1124073472 : Nat)<2147483647
    omega
  · exact lambda_canonical

#print axioms lambda_canonical
#print axioms transfer_lambda
#print axioms withdrawal_lambda
#print axioms transfer
#print axioms withdrawal
end R1Z.ProverRw18FieldFixtures
