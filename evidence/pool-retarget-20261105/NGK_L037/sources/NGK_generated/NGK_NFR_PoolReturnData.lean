import Lean
import NGK_NFR_RawInverse
import NGK_NFR_ResultForward
import NGK_NFR_CHelperBridge
import NGK_NFR_CSettlement
import NGK_NFR_ExtractedDecode

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_PoolReturnData
open Aeneas Aeneas.Std Result
open NGK_NFO_PoolReturnData
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

/-- Ruling (ab'): the accepted runtime row is only about nonempty replies.
The Context parameter is identical at write and read, with no intervening state. -/
def RuntimeReturnData {Context Key State : Type}
    (runtime : Runtime Context Key State) : Prop :=
  ∀ context program bytes, 1 ≤ bytes.length → bytes.length ≤ 1024 →
    runtime.read context (runtime.write context program bytes) = some (program,bytes)

/-- Accepted-run composition: acceptance is the event being analysed, not a
new runtime or codec premise. Decoder inversion is proved by raw_inverse. -/
theorem accepted_association {Context Key RuntimeState Accounts Other : Type} [DecidableEq Key]
    (runtime : Runtime Context Key RuntimeState) (law : RuntimeReturnData runtime)
    (context : Context) (selected : Key)
    (state : AspisR1.S2I.ReturnData.State Accounts Other) (s : NFY_NEU_EmitModel.Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()))
    (value : NGK_NFO_ReadModel.Accepted) (events : List NGK_NFO_ReadModel.Event)
    (accepted : NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read context (runtime.write context selected
        (AspisR1.S2K.ResultPayload.bytes s).val)) NGK_NFO_PacketDecoder.run =
      ok (.Ok value,events)) :
    AspisR1.NFY_JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes))
      state s = ok (.Ok (AspisR1.S2I.ReturnData.set state
        (AspisR1.S2K.ResultPayload.bytes s).val)) ∧
    value.value = AspisR1.S2K.ResultAdmission.value s ∧
    value.bytes = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    (NGK_NFO_ResultLayout.bytes value.value).val = value.bytes ∧
    events = [.clear,.invoke,.read,.decode] ∧
    NFY_NEY_EmitComposed.encode value.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) ∧
    NGK_NFR_CHelper.terminal_ref NFY_NEY_EmitComposed.encode value.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) := by
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  have read := law context selected (AspisR1.S2K.ResultPayload.bytes s).val
    (by rw [width]; decide) (by rw [width]; decide)
  rw [read] at accepted
  obtain ⟨_,bytes,returned,length,decoded,saved,trace⟩ :=
    NGK_NFO_ReadAccepted.accepted selected (.Ok ()) _ NGK_NFO_PacketDecoder.run value events accepted
  have pairEq := Option.some.inj returned
  have bytesEq := congrArg Prod.snd pairEq
  have encoded := NGK_NFR_RawInverse.accepted_codec bytes value.value length decoded
  have encodedArray : NGK_NFO_ResultLayout.bytes value.value = AspisR1.S2K.ResultPayload.bytes s :=
    Subtype.ext (encoded.trans bytesEq.symm)
  have same : value.value = AspisR1.S2K.ResultAdmission.value s :=
    NGK_NFO_ResultInjective.injective _ _ (encodedArray.trans (NGK_NFO_ResultLayout.emitted s).symm)
  exact ⟨AspisR1.NFY_JHb_Emit.accepted _ (fun _ _ => rfl) state s valid,
    same,saved.trans bytesEq.symm,encoded.trans saved.symm,trace,
    NGK_NFR_CSettlement.reencode_same s value same valid,
    NGK_NFR_CHelperBridge.same_emission s value same valid⟩
#print axioms accepted_association
/-- Forward association: the decoder's accepting return is derived for every
valid emitted statement. There is no independent accepted-read premise. -/
theorem association {Context Key RuntimeState Accounts Other : Type} [DecidableEq Key]
    (runtime : Runtime Context Key RuntimeState) (law : RuntimeReturnData runtime)
    (context : Context) (selected : Key)
    (state : AspisR1.S2I.ReturnData.State Accounts Other) (s : NFY_NEU_EmitModel.Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    AspisR1.NFY_JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes))
      state s = ok (.Ok (AspisR1.S2I.ReturnData.set state
        (AspisR1.S2K.ResultPayload.bytes s).val)) ∧
    NGK_NFO_ReadModel.run selected (.Ok ())
      (runtime.read context (runtime.write context selected
        (AspisR1.S2K.ResultPayload.bytes s).val)) NGK_NFO_PacketDecoder.run =
      ok (.Ok ⟨AspisR1.S2K.ResultAdmission.value s,
          (AspisR1.S2K.ResultPayload.bytes s).val⟩,
        [.clear,.invoke,.read,.decode]) ∧
    NFY_NEY_EmitComposed.encode (AspisR1.S2K.ResultAdmission.value s) =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) ∧
    NGK_NFR_CHelper.terminal_ref NFY_NEY_EmitComposed.encode
      (AspisR1.S2K.ResultAdmission.value s) =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) := by
  have width := (AspisR1.S2K.ResultPayload.bytes s).property
  refine ⟨AspisR1.NFY_JHb_Emit.accepted _ (fun _ _ => rfl) state s valid,?_,?_,?_⟩
  · rw [law context selected _ (by rw [width]; decide) (by rw [width]; decide)]
    exact NGK_NFO_ReadModel.decoded selected _ NGK_NFO_PacketDecoder.run _ width
      (NGK_NFR_ResultForward.emitted s valid)
  · exact NGK_NFR_CSettlement.reencode_same s
      ⟨AspisR1.S2K.ResultAdmission.value s,(AspisR1.S2K.ResultPayload.bytes s).val⟩ rfl valid
  · exact NGK_NFR_CHelperBridge.same_emission s
      ⟨AspisR1.S2K.ResultAdmission.value s,(AspisR1.S2K.ResultPayload.bytes s).val⟩ rfl valid
#print axioms association
end NGK_NFR_PoolReturnData

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
