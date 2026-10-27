import R1Z.PV_RunJoin_AdmittedPayload20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedPackage20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_CompilerDictionary16.shipped
local notation "M" => PV_RunJoin_FixtureRecords.M

/-- Same i throughout; the compiled payload association is explicit, not a replacement input. -/
theorem transfer (i : PV_Src_NativeInput.Input)
    (hr : i.request = transferRequest) (hw : i.witness = witness)
    (hc : i.change = transferChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot) :
    i.compiled = PV_RunJoin_TransferPayload20.output ↔
    (@PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) ∧
    PV_Src_NativeInput.transition i.compiled.public_statement = PV_RunJoin_RecordedTransfer.transition ∧
    PV_Src_NativeInput.publicInput i = PV_RunJoin_RecordedTransfer.publicInput ∧
    ∃ w : AspisR1.SpendRelation.Wspend,
      BuilderSpendRelation.RspendPlus (PV_RunJoin_FixtureRecords.fixturePublic false) w ∧
      ∀ c r, liftU (K := M) (PV_Src_Forest_Columns.read i.compiled.semantic_c1.c1 c r) =
        R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic false)
          (BuilderSpendRelation.modelWitness w) c r := by
  constructor
  · intro he
    have hrun := (PV_RunJoin_NativeReturn20.transfer_selected_iff i hr hw hc hl hs).mpr he
    refine ⟨hrun,PV_RunJoin_NativeReturn20.transfer_transition i hr hw hc hl hs hrun,
      PV_RunJoin_NativeReturn20.transfer_public i hr hw hc hl hs hrun,?_⟩
    rw [he]
    exact PV_RunJoin_AdmittedPayload20.transfer
  · intro h
    exact (PV_RunJoin_NativeReturn20.transfer_selected_iff i hr hw hc hl hs).mp h.1
#print axioms transfer

/-- Same i throughout; the compiled payload association is explicit, not a replacement input. -/
theorem withdrawal (i : PV_Src_NativeInput.Input)
    (hr : i.request = withdrawalRequest) (hw : i.witness = witness)
    (hc : i.change = withdrawalChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot) :
    i.compiled = PV_RunJoin_WithdrawalPayload20.output ↔
    (@PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) ∧
    PV_Src_NativeInput.transition i.compiled.public_statement = PV_RunJoin_RecordedWithdrawal.transition ∧
    PV_Src_NativeInput.publicInput i = PV_RunJoin_RecordedWithdrawal.publicInput ∧
    ∃ w : AspisR1.SpendRelation.Wspend,
      BuilderSpendRelation.RspendPlus (PV_RunJoin_FixtureRecords.fixturePublic true) w ∧
      ∀ c r, liftU (K := M) (PV_Src_Forest_Columns.read i.compiled.semantic_c1.c1 c r) =
        R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic true)
          (BuilderSpendRelation.modelWitness w) c r := by
  constructor
  · intro he
    have hrun := (PV_RunJoin_NativeReturn20.withdrawal_selected_iff i hr hw hc hl hs).mpr he
    refine ⟨hrun,PV_RunJoin_NativeReturn20.withdrawal_transition i hr hw hc hl hs hrun,
      PV_RunJoin_NativeReturn20.withdrawal_public i hr hw hc hl hs hrun,?_⟩
    rw [he]
    exact PV_RunJoin_AdmittedPayload20.withdrawal
  · intro h
    exact (PV_RunJoin_NativeReturn20.withdrawal_selected_iff i hr hw hc hl hs).mp h.1
#print axioms withdrawal
end R1Z.PV_RunJoin_SelectedPackage20
