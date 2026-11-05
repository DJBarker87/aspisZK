import NIB_Emission

set_option autoImplicit false
noncomputable section
namespace NIB_Association
open Aeneas Aeneas.Std Result NGK_NFO_PoolReturnData

/-- The plan's accepted decoder identifies the SAME result without assuming
statement validity, an encoder domain, or equality of successful outputs. -/
theorem accepted_read {Invocation Context Key RuntimeState : Type} [DecidableEq Key]
    (runtime : Runtime Context Key RuntimeState)
    (law : NGK_NFR_PoolReturnData.RuntimeReturnData runtime)
    (emitInvocation poolInvocation : Invocation) (context : Invocation → Context)
    (program : Invocation → Key) (selected : Key) (readState : RuntimeState)
    (s : NFY_NEU_EmitModel.Statement)
    (sameCpi : poolInvocation = emitInvocation)
    (selectedProgram : program emitInvocation = selected)
    (noInterveningCpi : readState = runtime.write (context emitInvocation)
      (program emitInvocation) (AspisR1.S2K.ResultPayload.bytes s).val)
    (authenticated : NGK_NFO_ReadModel.Accepted) (events : List NGK_NFO_ReadModel.Event)
    (acceptedDecoder : NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read (context poolInvocation) readState) NGK_NFO_PacketDecoder.run =
      ok (.Ok authenticated,events)) :
    authenticated.value = AspisR1.S2K.ResultAdmission.value s ∧
    authenticated.bytes = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    events = [.clear,.invoke,.read,.decode] := by
  rw [sameCpi,noInterveningCpi,selectedProgram] at acceptedDecoder
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  have returned := law (context emitInvocation) selected
    (AspisR1.S2K.ResultPayload.bytes s).val
    (by rw [width]; decide) (by rw [width]; decide)
  rw [returned] at acceptedDecoder
  obtain ⟨_,bytes,observed,length,decoded,saved,trace⟩ :=
    NGK_NFO_ReadAccepted.accepted selected (.Ok ()) _ NGK_NFO_PacketDecoder.run
      authenticated events acceptedDecoder
  have bytesEq := congrArg Prod.snd (Option.some.inj observed)
  have encoded := NGK_NFR_RawInverse.accepted_codec bytes authenticated.value length decoded
  have arrayEq : NGK_NFO_ResultLayout.bytes authenticated.value = AspisR1.S2K.ResultPayload.bytes s :=
    Subtype.ext (encoded.trans bytesEq.symm)
  exact ⟨NGK_NFO_ResultInjective.injective _ _
    (arrayEq.trans (NGK_NFO_ResultLayout.emitted s).symm),saved.trans bytesEq.symm,trace⟩
#print axioms accepted_read
end NIB_Association
