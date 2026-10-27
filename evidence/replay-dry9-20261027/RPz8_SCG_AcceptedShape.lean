import RPz8_SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_AcceptedShape
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open GExq_AccountExperiment

/-- The acceptance flag yields successful IDEAL wrapper replies. It does
not identify these replies with the partial native syscall execution. -/
theorem replies {A : Type} (o : Outcome A)
    (accepted : SCE_Experiment.accepted o = true) :
    ∃ saved post final next post2 final2,
      o.2.1 = ok (.Ok (saved,post,final)) ∧
      o.2.2 = some (next,ok (.Ok (post2,final2))) := by
  rcases o with ⟨i,reply,second⟩
  cases reply with
  | fail e => cases accepted
  | div => cases accepted
  | ok r =>
    cases r with
    | Err e => cases accepted
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      cases second with
      | none => cases accepted
      | some pair =>
        rcases pair with ⟨next,result⟩
        cases result with
        | fail e => cases accepted
        | div => cases accepted
        | ok r =>
          cases r with
          | Err e => cases accepted
          | Ok value =>
            rcases value with ⟨post2,final2⟩
            exact ⟨saved,post,final,next,post2,final2,rfl,rfl⟩

#print axioms replies
end AspisR1.SCG_AcceptedShape
end
