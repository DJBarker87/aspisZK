import NFR_RawInverse
import NFR_ExtractedDecode
set_option autoImplicit false
noncomputable section
namespace NFR_PoolReturnData
open Aeneas Aeneas.Std Result
open NFO_PoolReturnData
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

/-- Ruling (ab'): the accepted runtime row is only about nonempty replies.
The Context parameter is identical at write and read, with no intervening state. -/
def RuntimeReturnData {Context Key State : Type}
    (runtime : Runtime Context Key State) : Prop :=
  ∀ context program bytes, 1 ≤ bytes.length → bytes.length ≤ 1024 →
    runtime.read context (runtime.write context program bytes) = some (program,bytes)

/-- Accepted-run composition: acceptance is the event being analysed, not a
new runtime or codec premise. Decoder inversion is proved by raw_inverse. -/
theorem association {Context Key RuntimeState Accounts Other : Type} [DecidableEq Key]
    (runtime : Runtime Context Key RuntimeState) (law : RuntimeReturnData runtime)
    (context : Context) (selected : Key)
    (state : AspisR1.S2I.ReturnData.State Accounts Other) (s : NEU_EmitModel.Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()))
    (value : NFO_ReadModel.Accepted) (events : List NFO_ReadModel.Event)
    (accepted : NFO_ReadModel.run selected (.Ok ())
      (runtime.read context (runtime.write context selected
        (AspisR1.S2K.ResultPayload.bytes s).val)) NFO_PacketDecoder.run =
      ok (.Ok value,events)) :
    AspisR1.JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes))
      state s = ok (.Ok (AspisR1.S2I.ReturnData.set state
        (AspisR1.S2K.ResultPayload.bytes s).val)) ∧
    value.value = AspisR1.S2K.ResultAdmission.value s ∧
    value.bytes = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    (NFO_ResultLayout.bytes value.value).val = value.bytes ∧
    events = [.clear,.invoke,.read,.decode] := by
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  have read := law context selected (AspisR1.S2K.ResultPayload.bytes s).val
    (by rw [width]; decide) (by rw [width]; decide)
  rw [read] at accepted
  obtain ⟨_,bytes,returned,length,decoded,saved,trace⟩ :=
    NFO_ReadAccepted.accepted selected (.Ok ()) _ NFO_PacketDecoder.run value events accepted
  have pairEq := Option.some.inj returned
  have bytesEq := congrArg Prod.snd pairEq
  have encoded := NFR_RawInverse.accepted_codec bytes value.value length decoded
  have encodedArray : NFO_ResultLayout.bytes value.value = AspisR1.S2K.ResultPayload.bytes s :=
    Subtype.ext (encoded.trans bytesEq.symm)
  have same : value.value = AspisR1.S2K.ResultAdmission.value s :=
    NFO_ResultInjective.injective _ _ (encodedArray.trans (NFO_ResultLayout.emitted s).symm)
  exact ⟨AspisR1.JHb_Emit.accepted _ (fun _ _ => rfl) state s valid,
    same,saved.trans bytesEq.symm,encoded.trans saved.symm,trace⟩
#print axioms association
end NFR_PoolReturnData
