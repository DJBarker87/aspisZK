import RPz7_GExq_OuterLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_EventGood
open Aeneas Aeneas.Std Result GExq_OuterLower

def admissible (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : S2W_Trace.Event → Prop
  | .returned call _ => GExq_ChildCode.Admissible hashv call

theorem on_run {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (code : Native A) (good : Good hashv code)
    (before after : S2W_Trace.Log) (value : A)
    (initial : ∀ e ∈ before, admissible hashv e)
    (ran : S2W_Trace.run sdk code before = ok (value,after)) :
    ∀ e ∈ after, admissible hashv e := by
  induction code generalizing before after with
  | done a => cases Result.ok.inj ran; exact initial
  | step r k ih => cases r with
    | fail e => cases ran
    | div => cases ran
    | ok a => exact ih a good before after initial ran
  | call op k ih =>
    cases actual : S2W_Trace.invoke sdk op with
    | fail e => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | div => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | ok a =>
      simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran
      apply ih a (good.2 a) (before ++ [.returned op a]) after ?_ ran
      intro e member
      rcases List.mem_append.mp member with old | fresh
      · exact initial e old
      · obtain rfl := List.mem_singleton.mp fresh
        exact good.1

#print axioms on_run
end AspisR1.GExq_EventGood
end
