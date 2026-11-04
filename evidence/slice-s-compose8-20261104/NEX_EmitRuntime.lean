import NEU_EmitModel
import NEX_ReturnData
set_option autoImplicit false
noncomputable section
namespace NEX_EmitRuntime
open Aeneas Aeneas.Std Result
open NEU_EmitModel
/-- Ruling (ab): this trace-bearing runtime instance adds RuntimeReturnData.
BindingBridge and EncoderBridge remain explicit native obligations. -/
theorem result_state_effects {A E : Type}
    (binding : Statement → Output → Result (core.result.Result Unit NEU_EmitModel.Error))
    (encode : Output → Result (core.result.Result Bytes NEU_EmitModel.Error))
    (bindingBridge : BindingBridge binding) (encoderBridge : EncoderBridge encode)
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run binding encode (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s =
    AspisR1.JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s :=
  NEU_EmitModel.result_state_effects binding encode bindingBridge encoderBridge _ state s

/-- Exact event position and no later write in the successful modeled path.
The native root association and native children are not supplied by this law. -/
theorem success {A E : Type}
    (binding : Statement → Output → Result (core.result.Result Unit NEU_EmitModel.Error))
    (encode : Output → Result (core.result.Result Bytes NEU_EmitModel.Error))
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) (bytes : Bytes)
    (hb : binding s (derived s) = ok (.Ok ()))
    (he : encode (derived s) = ok (.Ok bytes))
    (header : bytes.val.take 4 = [65#u8,83#u8,82#u8,56#u8]) :
    run binding encode (fun st raw => ok (AspisR1.S2I.ReturnData.set st raw)) state s =
    ok (.Ok (AspisR1.S2I.ReturnData.set state bytes.val)) := by
  unfold run
  rw [hb]
  simp only [bind_tc_ok]
  rw [he]
  simp only [bind_tc_ok]
  have hlen : bytes.val.length = 792 := bytes.property
  simp only [hlen, header, ne_eq, not_true_eq_false, ite_false, bind_tc_ok]

#print axioms result_state_effects
#print axioms success
end NEX_EmitRuntime
