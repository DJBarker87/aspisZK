import GExq_ContainingRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_OuterLog
open Aeneas Aeneas.Std Result GExq_OuterLower CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def event (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {A : Type} → S2W_Trace.Call A → Oracle A) : S2W_Trace.Event → List (Bytes × State)
  | .returned call _ => SdkC_Source.readLog (SdkC_Source.run hashv (impl call) []).2

def trace (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {A : Type} → S2W_Trace.Call A → Oracle A) (log : S2W_Trace.Log) :=
  log.flatMap (event hashv impl)

/-- Exact ordered flattening of an accepted enclosing native trace. Unlike
read containment this retains duplicate reads and the location of every child. -/
theorem flatten {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) (before after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run sdk code before = ok (value,after)) :
    trace hashv impl before ++ SdkC_Source.readLog (SdkC_Source.run hashv (lower impl code) []).2 =
      trace hashv impl after := by
  induction code generalizing before after with
  | done a =>
    cases Result.ok.inj ran
    exact List.append_nil _
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
      have erased : S2W_Trace.erase sdk (.call op k) = ok value := by
        rw [← S2W_Trace.erase_run sdk (.call op k) before,ran]
        rfl
      have total := (GExq_OuterLower.erasure sdk hashv impl law (.call op k) good).trans erased
      obtain ⟨chosen,called,_,logs⟩ := GExq_CodeTrace.success_bind hashv (impl op)
        (fun b => lower impl (k b)) value total
      have same : chosen = a := Result.ok.inj (called.symm.trans ((law op good.1).trans actual))
      subst chosen
      simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran
      have next := ih a (good.2 a) (before ++ [.returned op a]) after ran
      change trace hashv impl before ++
        SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Effect.bind (impl op)
          (fun b => lower impl (k b))) []).2 = _
      rw [logs]
      simpa only [trace,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,event,
        List.append_nil,List.append_assoc] using next

#print axioms flatten
end AspisR1.SCG_OuterLog
end
