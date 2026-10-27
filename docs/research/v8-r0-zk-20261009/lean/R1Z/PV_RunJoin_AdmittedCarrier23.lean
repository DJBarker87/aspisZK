import R1Z.PV_RunJoin_UniversalBuild22
import R1Z.PV_RunJoin_NativeFibre21
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AdmittedCarrier23
open Aeneas Aeneas.Std Result PV_Src_NativeInput
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Raw data at the two recorded successful calls, for non-vacuity only. -/
def transfer : Input :=
  ⟨transferRequest,witness,transferChange,laneAnchor,snapshot,PV_RunJoin_TransferPayload20.output⟩
def withdrawal : Input :=
  ⟨withdrawalRequest,witness,withdrawalChange,laneAnchor,snapshot,PV_RunJoin_WithdrawalPayload20.output⟩

theorem transfer_return : @run E R transfer = ok (.Ok transfer.compiled) :=
  PV_RunJoin_NativeReturn20.transfer_call transfer rfl rfl rfl rfl rfl
#print axioms transfer_return

theorem withdrawal_return : @run E R withdrawal = ok (.Ok withdrawal.compiled) :=
  PV_RunJoin_NativeReturn20.withdrawal_call withdrawal rfl rfl rfl rfl rfl
#print axioms withdrawal_return

theorem model_injective : Function.Injective
    (BuilderSpendRelation.modelWitness (K := R1J.SpendWitnessMap.F)) := by
  intro a b h
  have e := congrArg (fun m : R0Z.BuilderModel.ModelWitness R1J.SpendWitnessMap.F =>
    ({inputValue := m.inputValue, outputValue := m.outputValue, changeValue := m.changeValue,
      sk := m.sk, salt := m.salt, path := m.path,
      pair := ⟨m.pairFirst,m.pairOccupied,m.pairSecond,m.pairInverse⟩,
      recipientOwner := m.recipientOwner, recipientSalt := m.recipientSalt,
      changeOwner := m.changeOwner, changeSalt := m.changeSalt} : AspisR1.SpendRelation.Wspend)) h
  exact e
#print axioms model_injective

theorem transfer_witness : BuilderRecordCanonical.witness
    (PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_RunJoin_UniversalBuild22.records transfer).w) =
      PV_RunJoin_FixtureRecords.witness false := by
  apply model_injective
  exact (BuilderRecordCanonical.witness_model _).trans PV_RunJoin_TransferWitness20.source
#print axioms transfer_witness

theorem withdrawal_witness : BuilderRecordCanonical.witness
    (PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_RunJoin_UniversalBuild22.records withdrawal).w) =
      PV_RunJoin_WithdrawalWitness20.witness := by
  apply model_injective
  exact (BuilderRecordCanonical.witness_model _).trans PV_RunJoin_WithdrawalWitness20.source
#print axioms withdrawal_witness

theorem transfer_public : publicInput transfer = PV_RunJoin_RecordedTransfer.publicInput :=
  PV_RunJoin_NativeReturn20.transfer_public transfer rfl rfl rfl rfl rfl transfer_return
#print axioms transfer_public

theorem withdrawal_public : publicInput withdrawal = PV_RunJoin_RecordedWithdrawal.publicInput :=
  PV_RunJoin_NativeReturn20.withdrawal_public withdrawal rfl rfl rfl rfl rfl withdrawal_return
#print axioms withdrawal_public

theorem transfer_admitted : PV_RunJoin_UniversalBuild22.Admission (K := K) transfer := by
  unfold PV_RunJoin_UniversalBuild22.Admission
  rw [transfer_public,PV_RunJoin_CanonicalPublic21.transfer,transfer_witness]
  exact PV_RunJoin_FixtureFibres.lift_spendPlus _ _
    (PV_RunJoin_FixtureRecords.transfer_spendPlus PV_RunJoin_TransferSentinel.nonzero)
#print axioms transfer_admitted

theorem withdrawal_admitted : PV_RunJoin_UniversalBuild22.Admission (K := K) withdrawal := by
  unfold PV_RunJoin_UniversalBuild22.Admission
  rw [withdrawal_public,PV_RunJoin_CanonicalPublic21.withdrawal,withdrawal_witness]
  exact PV_RunJoin_FixtureFibres.lift_spendPlus _ _ PV_RunJoin_WithdrawalWitness20.admission
#print axioms withdrawal_admitted

/-- This explicitly changes the raw source domain to an admitted subtype.
It is not an unguarded theorem about the original raw Input source. -/
abbrev Admitted := {i : Input // PV_RunJoin_UniversalBuild22.Admission (K := K) i}

theorem public_eq : ∀ w : Admitted (K := K),
    (PV_Src_NativeIdentification.prover (K := K) (fun i : Admitted (K := K) => i.val)
      PV_Src_Transport.transport).public w =
    BuilderSource.prover.public
      (PV_RunJoin_UniversalBuild22.toInstance (fun i : Admitted (K := K) => i.val)
        (fun i => i.property) w) :=
  PV_RunJoin_UniversalBuild22.public_eq _ _ (fun i => i.property)
#print axioms public_eq

theorem nonempty_both : ∃ wt ww : Admitted (K := K),
    wt.val = transfer ∧ ww.val = withdrawal :=
  ⟨⟨transfer,transfer_admitted⟩,⟨withdrawal,withdrawal_admitted⟩,rfl,rfl⟩
#print axioms nonempty_both
end R1Z.PV_RunJoin_AdmittedCarrier23
