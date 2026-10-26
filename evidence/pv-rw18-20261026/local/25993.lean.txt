import R1Z.ProverRw18FinalPower16
import R1Z.ProverRw18FieldFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FixturePower
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning ProverRw18FixtureSamples
variable [ProverRwFull.ExternalTypes]

theorem transfer (ops : ProverRwFull.ExternalFuns) (out : Q) :
    ProverRwDictionaryTower.mapResult Prod.snd
      (PV_RW_IteratorStateLoop.run ops transfer_lambda
        (⟨Array.to_slice transfer_values,0⟩ : core.slice.iter.Iter U32) (out,transfer_lambda))=
          ok (full (ProverRw18FieldEncode.encode ((decode ProverRw18FieldFixtures.lambda)^17))) := by
  rw [← ProverRw18FieldFixtures.transfer_lambda]
  exact ProverRw18FinalPower16.combined ops transfer_values _ out ProverRw18FieldFixtures.lambda_canonical

theorem withdrawal (ops : ProverRwFull.ExternalFuns) (out : Q) :
    ProverRwDictionaryTower.mapResult Prod.snd
      (PV_RW_IteratorStateLoop.run ops withdrawal_lambda
        (⟨Array.to_slice withdrawal_values,0⟩ : core.slice.iter.Iter U32) (out,withdrawal_lambda))=
          ok (full (ProverRw18FieldEncode.encode ((decode ProverRw18FieldFixtures.lambda)^17))) := by
  rw [← ProverRw18FieldFixtures.withdrawal_lambda]
  exact ProverRw18FinalPower16.combined ops withdrawal_values _ out ProverRw18FieldFixtures.lambda_canonical

#print axioms transfer
#print axioms withdrawal
end R1Z.ProverRw18FixturePower
