import NIB_Emission

set_option autoImplicit false
noncomputable section
namespace NIB_EmissionFrame
open Aeneas Aeneas.Std Result

/-- Exact emitter frame, with the set-return-data event retained. Accounts can
contain the full heap and metadata. This does not frame the Pool continuation. -/
theorem frame_of_success {A E : Type}
    (state after : AspisR1.S2I.ReturnData.State A E) (s : NFY_NEU_EmitModel.Statement)
    (emitted : AspisR1.NFY_JHb_Emit.source
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s = ok (.Ok after)) :
    after.accounts = state.accounts ∧
    after.returnData = (AspisR1.S2K.ResultPayload.bytes s).val ∧
    after.events = state.events ++
      [.setReturnData (AspisR1.S2K.ResultPayload.bytes s).val] := by
  have valid := NIB_Emission.valid_of_success state after s emitted
  have canonical := AspisR1.NFY_JHb_Emit.accepted _ (fun _ _ => rfl) state s valid
  rw [emitted] at canonical
  have same := core.result.Result.Ok.inj (Result.ok.inj canonical)
  have accounts := congrArg AspisR1.S2I.ReturnData.State.accounts same
  have data := congrArg AspisR1.S2I.ReturnData.State.returnData same
  have events := congrArg AspisR1.S2I.ReturnData.State.events same
  exact ⟨accounts,data,events⟩
#print axioms frame_of_success
end NIB_EmissionFrame
