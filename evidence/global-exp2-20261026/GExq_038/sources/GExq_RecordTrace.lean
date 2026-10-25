import GExq_OuterRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_RecordTrace
open Aeneas Aeneas.Std Result GExq_OuterLower GExq_OuterRecord

def projectLog (log : S2W_Trace.Log) : List Event :=
  log.flatMap fun event => match event with | .returned call value => project call value

theorem project_append (left right : S2W_Trace.Log) :
    projectLog (left ++ right) = projectLog left ++ projectLog right := List.flatMap_append

theorem source {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) (before after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run sdk code before = ok (value,after)) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (record impl code (projectLog before)) = ok (value,projectLog after) := by
  induction code generalizing before after with
  | done a =>
    have same := Result.ok.inj ran
    cases same
    rfl
  | step r k ih =>
    cases r with
    | fail e => cases ran
    | div => cases ran
    | ok a => exact ih a good before after ran
  | call op k ih =>
    cases actual : S2W_Trace.invoke sdk op with
    | fail e => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | div => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | ok a =>
      simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran
      have next := ih a (good.2 a) (before ++ [.returned op a]) after ran
      simp only [record,erase_bind_explicit,law op good.1,actual,bind_tc_ok]
      simpa only [project_append,projectLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using next

#print axioms project_append
#print axioms source
end AspisR1.GExq_RecordTrace
end
