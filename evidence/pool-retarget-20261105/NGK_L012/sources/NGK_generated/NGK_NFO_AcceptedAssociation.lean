import Lean
import NGK_NFO_PoolReturnData
import NGK_NFO_ReadAccepted
import NGK_NFO_PacketDecoder
import NGK_NFO_ResultInjective

set_option autoImplicit false
noncomputable section
namespace NGK_NFO_AcceptedAssociation
open Aeneas Aeneas.Std Result
open NGK_NFO_PoolReturnData

/-- OPEN codec obligation at exactly the domain proved by the Pool gate.
This is accepted decoding/encoding inversion, not decoder totality or a
native/refinement assumption hidden in a carrier. -/
def AcceptedCodec : Prop :=
  ∀ bytes value, bytes.length = 792 →
    NGK_NFO_PacketDecoder.run bytes = ok (.Ok value) →
    (NGK_NFO_ResultLayout.bytes value).val = bytes

/-- Accepted-run MODEL association. The remaining codec premise is explicit.
The full native Pool carrier/ownership certificate is independently required
before this conditional mathematical fact receives hybrid closure credit. -/
theorem consumed {Context Key State : Type} [DecidableEq Key]
    (runtime : Runtime Context Key State) (law : RuntimeReturnData runtime)
    (codec : AcceptedCodec) (context : Context) (selected : Key)
    (s : NFY_NEU_EmitModel.Statement) (value : NGK_NFO_ReadModel.Accepted)
    (events : List NGK_NFO_ReadModel.Event)
    (accepted : NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read context (runtime.write context selected
        (AspisR1.S2K.ResultPayload.bytes s).val)) NGK_NFO_PacketDecoder.run =
      ok (.Ok value,events)) :
    value.value = AspisR1.S2K.ResultAdmission.value s ∧
    value.bytes = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    events = [.clear,.invoke,.read,.decode] := by
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  have read := law context selected (AspisR1.S2K.ResultPayload.bytes s).val (by rw [width]; decide)
  rw [read] at accepted
  obtain ⟨_,bytes,returned,length,decoded,saved,trace⟩ :=
    NGK_NFO_ReadAccepted.accepted selected (.Ok ()) _ NGK_NFO_PacketDecoder.run value events accepted
  have pairEq := Option.some.inj returned
  have bytesEq := congrArg Prod.snd pairEq
  have encoded := codec bytes value.value length decoded
  have encodedArray : NGK_NFO_ResultLayout.bytes value.value = AspisR1.S2K.ResultPayload.bytes s :=
    Subtype.ext (encoded.trans bytesEq.symm)
  have same : value.value = AspisR1.S2K.ResultAdmission.value s :=
    NGK_NFO_ResultInjective.injective _ _ (encodedArray.trans (NGK_NFO_ResultLayout.emitted s).symm)
  exact ⟨same,saved.trans bytesEq.symm,trace⟩
#print axioms consumed
end NGK_NFO_AcceptedAssociation

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
