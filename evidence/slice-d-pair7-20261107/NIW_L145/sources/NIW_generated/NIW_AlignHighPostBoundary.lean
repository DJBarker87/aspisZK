import NIW_AlignPartialPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignHighPostBoundary
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

def Call (c : Context) (w : Ref W) (parts : Parts) : RP → Option (Result (RU×Parts))
 | .Err _ => none
 | .Ok values => some (FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts)

theorem observed (c : Context) (w : Ref W) (parts : Parts) (reply : RP) :
 (NIW_AlignPartialPhase.run c w parts reply).2.high=Call c w parts reply := by
 cases reply with
 | Err err => rfl
 | Ok values =>
  cases call : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts with
  | fail err => simp only [NIW_AlignPartialPhase.run,call,Call]
  | div => simp only [NIW_AlignPartialPhase.run,call,Call]
  | ok value => rcases value with ⟨returned,after⟩;simp only [NIW_AlignPartialPhase.run,call,Call]

def Post (before : Parts) : Option (Result (RU×Parts)) → Prop
 | some (ok (_,after)) => canonical after ∧ NHX_HighPost.Frame before after
 | _ => True

/-- Actual high writes and full frame, even on returned Err. There is no
successful-high premise and no fact about an unentered high call. -/
theorem source (c : Context) (w : Ref W) (parts : Parts) (reply : RP)
 (hf : NHI_TensorOuterStep.Factors w.value) (c0 : canonical c.ap0.value)
 (c1 : canonical c.ap1.value) (cp : canonical parts) :
 Post parts (NIW_AlignPartialPhase.run c w parts reply).2.high := by
 rw [observed]
 cases reply with
 | Err err => trivial
 | Ok values =>
  cases call : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts with
  | fail err => trivial
  | div => trivial
  | ok value =>
   rcases value with ⟨returned,after⟩
   exact NIG_PairFrames.high values w.value c.ap0.value c.ap1.value parts after hf c0 c1 cp returned call

#print axioms observed
#print axioms source
end AspisR1.NIW_AlignHighPostBoundary
