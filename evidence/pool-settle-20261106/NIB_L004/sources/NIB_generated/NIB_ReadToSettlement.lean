import NIB_Association

set_option autoImplicit false
noncomputable section
namespace NIB_ReadToSettlement
open Aeneas Aeneas.Std Result NGK_NFO_PoolReturnData
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

/-- MODEL part of the adopted plan. Native owners must instantiate these
observations at the actual reached calls; this theorem supplies no CPI entry,
SDK borrow, or physical account-mutation certificate. No pending row is used. -/
theorem read_to_settlement
    {Invocation Context Key RuntimeState Accounts Other LaneImage : Type} [DecidableEq Key]
    (runtime : Runtime Context Key RuntimeState)
    (law : NGK_NFR_PoolReturnData.RuntimeReturnData runtime)
    (emitInvocation poolInvocation : Invocation) (context : Invocation → Context)
    (program : Invocation → Key) (selected : Key) (readState : RuntimeState)
    (state after : AspisR1.S2I.ReturnData.State Accounts Other)
    (s : NFY_NEU_EmitModel.Statement)
    (sameCpi : poolInvocation = emitInvocation)
    (selectedProgram : program emitInvocation = selected)
    (noInterveningCpi : readState = runtime.write (context emitInvocation)
      (program emitInvocation) (AspisR1.S2K.ResultPayload.bytes s).val)
    (emitted : AspisR1.NFY_JHb_Emit.source
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s = ok (.Ok after))
    (authenticated : NGK_NFO_ReadModel.Accepted) (events : List NGK_NFO_ReadModel.Event)
    (acceptedDecoder : NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read (context poolInvocation) readState) NGK_NFO_PacketDecoder.run =
      ok (.Ok authenticated,events))
    (validate : NGK_NFR_CSettlement.Output → Result (core.result.Result Unit NGK_NFR_CSettlement.Error))
    (lane : NGK_NFR_CSettlement.Output → Result (core.result.Result LaneImage NGK_NFR_CSettlement.Error))
    (image : LaneImage)
    (checked : validate authenticated.value = ok (.Ok ()))
    (advanced : lane authenticated.value = ok (.Ok image)) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) ∧
    validate (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok ()) ∧
    lane (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok image) ∧
    authenticated.value = AspisR1.S2K.ResultAdmission.value s ∧
    authenticated.bytes = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    events = [.clear,.invoke,.read,.decode] ∧
    1 ≤ authenticated.bytes.length ∧ authenticated.bytes.length ≤ 1024 ∧
    after = AspisR1.S2I.ReturnData.set state (AspisR1.S2K.ResultPayload.bytes s).val ∧
    NGK_NFR_CSettlement.run validate lane NFY_NEY_EmitComposed.encode authenticated =
      ok (.Ok (image,AspisR1.S2K.ResultPayload.bytes s),
        [.validate authenticated.value,.lane authenticated.value,.encode authenticated.value]) ∧
    NGK_NFV_HelperModel.run NFY_NEY_EmitComposed.encode authenticated.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s),
        [.encode authenticated.value,.allocate (AspisR1.S2K.ResultPayload.bytes s)]) := by
  have valid := NIB_Emission.valid_of_success state after s emitted
  obtain ⟨same,bytes,trace⟩ := NIB_Association.accepted_read runtime law
    emitInvocation poolInvocation context program selected readState s sameCpi selectedProgram
    noInterveningCpi authenticated events acceptedDecoder
  have checkedSame : validate (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok ()) := by
    rw [← same]; exact checked
  have advancedSame : lane (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok image) := by
    rw [← same]; exact advanced
  have joined := NGK_NFR_ModelJoin.same_emitted_settlement runtime law
    (context emitInvocation) selected state s valid validate lane image checkedSame advancedSame
  have afterEq : after = AspisR1.S2I.ReturnData.set state (AspisR1.S2K.ResultPayload.bytes s).val := by
    rw [emitted] at joined
    exact core.result.Result.Ok.inj (Result.ok.inj joined.1)
  have width : authenticated.bytes.length = 792 := by
    rw [bytes]; exact (AspisR1.S2K.ResultPayload.bytes s).property
  refine ⟨valid,checkedSame,advancedSame,same,bytes,trace,by omega,by omega,afterEq,?_,?_⟩
  · have settled := joined.2.2
    have record : authenticated =
        ⟨AspisR1.S2K.ResultAdmission.value s,(AspisR1.S2K.ResultPayload.bytes s).val⟩ := by
      cases authenticated
      simp_all only
    simpa only [record] using settled
  · exact NGK_NFV_HelperModel.same_emission s authenticated same valid
#print axioms read_to_settlement
end NIB_ReadToSettlement
