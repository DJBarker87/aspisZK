import NLI_FromFnInduction
import NLC_Suboccurrences
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_CallbackAssociation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- One native write consumes the SAME owned Claims value. This is the
source association part; the Kani value/frame windows and physical allocation
interpretation remain separately identified proof obligations. -/
theorem low {H : Type} (s : State H) (claims : Claims)
 (same : s.locals.claims=some claims) (i : Usize) (inside : i.val<16)
 (memory : NLI_FromFn.Memory) :
 (do let c ← read s.locals.claims
     (FinishModel.closureFn9 s.input.digest).call_mut c i)=
 ok (NKQ_MaskLowStep.lowAt claims i inside,claims) ∧
 NLI_FromFn.write memory i.val (NKQ_MaskLowStep.lowAt claims i inside) i.val=
 some (NKQ_MaskLowStep.lowAt claims i inside) := by
 exact ⟨NLC_Finish.low_callback s claims same i inside,by simp [NLI_FromFn.write]⟩
theorem high {H : Type} (s : State H) (claims : Claims)
 (same : s.locals.claims=some claims) (i : Usize) (inside : i.val<10)
 (memory : NLI_FromFn.Memory) :
 (do let c ← read s.locals.claims
     (FinishModel.closureFn5 s.input.digest).call_mut c i)=
 ok (NKQ_MaskHighStep.highAt claims i inside,claims) ∧
 NLI_FromFn.write memory i.val (NKQ_MaskHighStep.highAt claims i inside) i.val=
 some (NKQ_MaskHighStep.highAt claims i inside) := by
 exact ⟨NLC_Finish.high_callback s claims same i inside,by simp [NLI_FromFn.write]⟩
#print axioms low
#print axioms high
end AspisR1.NLI_CallbackAssociation
end
