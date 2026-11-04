import NFO_PoolReturnData
import NFO_ReadAccepted
import NFO_PacketDecoder
import NFO_ResultInjective
set_option autoImplicit false
noncomputable section
namespace NFO_AcceptedAssociation
open Aeneas Aeneas.Std Result
open NFO_PoolReturnData

/-- OPEN codec obligation at exactly the domain proved by the Pool gate.
This is accepted decoding/encoding inversion, not decoder totality or a
native/refinement assumption hidden in a carrier. -/
def AcceptedCodec : Prop :=
  ∀ bytes value, bytes.length = 792 →
    NFO_PacketDecoder.run bytes = ok (.Ok value) →
    (NFO_ResultLayout.bytes value).val = bytes

/-- Accepted-run MODEL association. The remaining codec premise is explicit.
The full native Pool carrier/ownership certificate is independently required
before this conditional mathematical fact receives hybrid closure credit. -/
theorem consumed {Context Key State : Type} [DecidableEq Key]
    (runtime : Runtime Context Key State) (law : RuntimeReturnData runtime)
    (codec : AcceptedCodec) (context : Context) (selected : Key)
    (s : NEU_EmitModel.Statement) (value : NFO_ReadModel.Accepted)
    (events : List NFO_ReadModel.Event)
    (accepted : NFO_ReadModel.run selected (.Ok ())
      (runtime.read context (runtime.write context selected
        (AspisR1.S2K.ResultPayload.bytes s).val)) NFO_PacketDecoder.run =
      ok (.Ok value,events)) :
    value.value = AspisR1.S2K.ResultAdmission.value s ∧
    value.bytes = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    events = [.clear,.invoke,.read,.decode] := by
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  have read := law context selected (AspisR1.S2K.ResultPayload.bytes s).val (by rw [width]; decide)
  rw [read] at accepted
  obtain ⟨_,bytes,returned,length,decoded,saved,trace⟩ :=
    NFO_ReadAccepted.accepted selected (.Ok ()) _ NFO_PacketDecoder.run value events accepted
  have pairEq := Option.some.inj returned
  have bytesEq := congrArg Prod.snd pairEq
  have encoded := codec bytes value.value length decoded
  have encodedArray : NFO_ResultLayout.bytes value.value = AspisR1.S2K.ResultPayload.bytes s :=
    Subtype.ext (encoded.trans bytesEq.symm)
  have same : value.value = AspisR1.S2K.ResultAdmission.value s :=
    NFO_ResultInjective.injective _ _ (encodedArray.trans (NFO_ResultLayout.emitted s).symm)
  exact ⟨same,saved.trans bytesEq.symm,trace⟩
#print axioms consumed
end NFO_AcceptedAssociation
