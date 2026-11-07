import NMS_Interpreted
import NMS_RSLError
set_option autoImplicit false
noncomputable section
namespace NMS_RawTry
open Aeneas Aeneas.Std AdapterRw
abbrev R (A : Type) := core.result.Result A solana_program_error.ProgramError

def simple {A B : Type} (m : RSL.Spec (R A)) (next : A → RSL.Spec (R B)) : RSL.Spec (R B) :=
 RSL.Spec.bind m (fun reply => match reply with
 | .Ok a => next a
 | .Err error => RSL.Spec.pure (.Err error))

def literal {A B : Type} (m : RSL.Spec (R A)) (next : A → RSL.Spec (R B)) : RSL.Spec (R B) := do
 let reply ← m
 let flow ← core.result.Result.Insts.CoreOpsTry.branch reply
 match flow with
 | .Continue a => next a
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    B (core.convert.FromSame solana_program_error.ProgramError) residual

theorem normalize {A B : Type} (m : RSL.Spec (R A)) (next : A → RSL.Spec (R B)) :
 literal m next = simple m next := by
 unfold literal simple
 apply congrArg (RSL.Spec.bind m)
 funext reply
 cases reply with
 | Ok a =>
   change RSL.Spec.bind (RSL.Spec.pure _) _ = _
   rw [RSL.Spec.bind_pure]
 | Err error =>
   change RSL.Spec.bind (RSL.Spec.pure _) _ = _
   rw [RSL.Spec.bind_pure]
   rfl

theorem simulates {A B C D : Type} (value : A → C) (output : B → D)
 (actual : RSL.Spec (R A)) (model : RSL.RS C)
 (next : A → RSL.Spec (R B)) (later : C → RSL.RS D)
 (first : NMS_Interpreted.Simulates (NMS_RSLError.reply value) actual model)
 (rest : ∀ a, NMS_Interpreted.Simulates (NMS_RSLError.reply output) (next a) (later (value a))) :
 NMS_Interpreted.Simulates (NMS_RSLError.reply output)
  (literal actual next) (RSL.RS.bind model later) := by
 rw [normalize]
 apply NMS_Interpreted.bind (NMS_RSLError.reply value) (NMS_RSLError.reply output) actual model _ _ first
 intro reply
 cases reply with
 | Ok a => exact rest a
 | Err e => exact NMS_Interpreted.pure _ _

#print axioms normalize
#print axioms simulates
end NMS_RawTry
