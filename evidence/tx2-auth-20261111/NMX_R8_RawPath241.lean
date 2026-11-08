import NMX_R8_SimulatesPath
set_option autoImplicit false
noncomputable section
namespace NMX_R8_RawPath241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

theorem full {A B C D : Type} (value : A → C) (output : B → D)
 (actual : RSL.Spec (NMS_R2N_RawTry.R A)) (model : RSL.RS C)
 (next : A → RSL.Spec (NMS_R2N_RawTry.R B)) (later : C → RSL.RS D)
 (first : Simulates (NMS_R2N_RSLError.reply value) actual model)
 (rest : ∀ env a events, actual env ⟨.ret (.Ok a),events⟩ →
   ∀ o, next a env o → later (value a) env (mapObs (NMS_R2N_RSLError.reply output) o)) :
 Simulates (NMS_R2N_RSLError.reply output) (NMS_R2N_RawTry.literal actual next) (RSL.RS.bind model later) := by
 rw [NMS_R2N_RawTry.normalize]
 apply NMX_R8_SimulatesPath.bind_using (NMS_R2N_RSLError.reply value) (NMS_R2N_RSLError.reply output)
  actual model _ _ first
 intro env reply events cut
 cases reply with
 | Ok a => exact rest env a events cut
 | Err e => exact NMS_R2N_Interpreted.pure _ _ env
#print axioms full
end NMX_R8_RawPath241
end
