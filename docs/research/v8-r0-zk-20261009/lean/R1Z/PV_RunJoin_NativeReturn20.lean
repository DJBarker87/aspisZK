import R1Z.PV_RunJoin_TransferPayload20
import R1Z.PV_RunJoin_WithdrawalPayload20
import R1Z.PV_RunJoin_SourceTransition20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeReturn20
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_CompilerDictionary16.shipped
theorem transfer_call (i : PV_Src_NativeInput.Input)
    (hr : i.request = transferRequest) (hw : i.witness = witness)
    (hc : i.change = transferChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot) :
    @PV_Src_NativeInput.run E R i = ok (.Ok PV_RunJoin_TransferPayload20.output) := by
  unfold PV_Src_NativeInput.run
  rw [hr,hw,hc,hl,hs]
  exact PV_RunJoin_TransferPayload20.source
#print axioms transfer_call

/-- The same selected i is preserved. Output association is an explicit P
obligation; it is not obtained by replacing Input.compiled. -/
theorem transfer_selected_iff (i : PV_Src_NativeInput.Input)
    (hr : i.request = transferRequest) (hw : i.witness = witness)
    (hc : i.change = transferChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot) :
    (@PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) ↔ i.compiled = PV_RunJoin_TransferPayload20.output := by
  constructor
  · intro h
    exact (core.result.Result.Ok.inj (Result.ok.inj ((transfer_call i hr hw hc hl hs).symm.trans h))).symm
  · intro h
    rw [h]
    exact transfer_call i hr hw hc hl hs
#print axioms transfer_selected_iff

theorem transfer_transition (i : PV_Src_NativeInput.Input)
    (hr : i.request = transferRequest) (hw : i.witness = witness)
    (hc : i.change = transferChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.transition i.compiled.public_statement = PV_RunJoin_RecordedTransfer.transition := by
  have he := (transfer_selected_iff i hr hw hc hl hs).mp hreturn
  rw [he]
  exact PV_RunJoin_SourceTransition20.transfer
#print axioms transfer_transition

theorem transfer_public (i : PV_Src_NativeInput.Input)
    (hr : i.request = transferRequest) (hw : i.witness = witness)
    (hc : i.change = transferChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.publicInput i = PV_RunJoin_RecordedTransfer.publicInput := by
  unfold PV_Src_NativeInput.publicInput
  rw [hr]
  simp only [PV_RunJoin_FixtureArguments.transferRequest]
  rw [transfer_transition i hr hw hc hl hs hreturn]
  rfl
#print axioms transfer_public

theorem transfer_semantic (i : PV_Src_NativeInput.Input)
    (hr : i.request = transferRequest) (hw : i.witness = witness)
    (hc : i.change = transferChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    i.compiled.semantic_c1.c1 = PV_RunJoin_SourceBanks19.transferBank.merged := by
  rw [(transfer_selected_iff i hr hw hc hl hs).mp hreturn]
  rfl
#print axioms transfer_semantic
theorem withdrawal_call (i : PV_Src_NativeInput.Input)
    (hr : i.request = withdrawalRequest) (hw : i.witness = witness)
    (hc : i.change = withdrawalChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot) :
    @PV_Src_NativeInput.run E R i = ok (.Ok PV_RunJoin_WithdrawalPayload20.output) := by
  unfold PV_Src_NativeInput.run
  rw [hr,hw,hc,hl,hs]
  exact PV_RunJoin_WithdrawalPayload20.source
#print axioms withdrawal_call

/-- The same selected i is preserved. Output association is an explicit P
obligation; it is not obtained by replacing Input.compiled. -/
theorem withdrawal_selected_iff (i : PV_Src_NativeInput.Input)
    (hr : i.request = withdrawalRequest) (hw : i.witness = witness)
    (hc : i.change = withdrawalChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot) :
    (@PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) ↔ i.compiled = PV_RunJoin_WithdrawalPayload20.output := by
  constructor
  · intro h
    exact (core.result.Result.Ok.inj (Result.ok.inj ((withdrawal_call i hr hw hc hl hs).symm.trans h))).symm
  · intro h
    rw [h]
    exact withdrawal_call i hr hw hc hl hs
#print axioms withdrawal_selected_iff

theorem withdrawal_transition (i : PV_Src_NativeInput.Input)
    (hr : i.request = withdrawalRequest) (hw : i.witness = witness)
    (hc : i.change = withdrawalChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.transition i.compiled.public_statement = PV_RunJoin_RecordedWithdrawal.transition := by
  have he := (withdrawal_selected_iff i hr hw hc hl hs).mp hreturn
  rw [he]
  exact PV_RunJoin_SourceTransition20.withdrawal
#print axioms withdrawal_transition

theorem withdrawal_public (i : PV_Src_NativeInput.Input)
    (hr : i.request = withdrawalRequest) (hw : i.witness = witness)
    (hc : i.change = withdrawalChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.publicInput i = PV_RunJoin_RecordedWithdrawal.publicInput := by
  unfold PV_Src_NativeInput.publicInput
  rw [hr]
  simp only [PV_RunJoin_FixtureArguments.withdrawalRequest]
  rw [withdrawal_transition i hr hw hc hl hs hreturn]
  rfl
#print axioms withdrawal_public

theorem withdrawal_semantic (i : PV_Src_NativeInput.Input)
    (hr : i.request = withdrawalRequest) (hw : i.witness = witness)
    (hc : i.change = withdrawalChange) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    i.compiled.semantic_c1.c1 = PV_RunJoin_SourceBanks19.withdrawalBank.merged := by
  rw [(withdrawal_selected_iff i hr hw hc hl hs).mp hreturn]
  rfl
#print axioms withdrawal_semantic
end R1Z.PV_RunJoin_NativeReturn20
