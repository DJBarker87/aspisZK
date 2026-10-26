import RPz7_GExq_ContainingRead
import RPz7_GExq_RecordLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_TraceLogs
open Aeneas Aeneas.Std Result GExq_OuterLower CheckpointBytes5Effect

def eventLog (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {A : Type} → S2W_Trace.Call A → Oracle A) : S2W_Trace.Event →
    List (AspisV8R19.DuplexFrames.Bytes × AspisV8R19.SourceDuplexStep.State)
  | .returned call _ => SdkC_Source.readLog (SdkC_Source.run hashv (impl call) []).2

def traceLog (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {A : Type} → S2W_Trace.Call A → Oracle A) (log : S2W_Trace.Log) :=
  log.flatMap (eventLog hashv impl)

/-- Exact chronological concatenation; includes every duplicate query in each
actually returning child and makes no acceptance-only query deletion. -/
theorem ordered {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) (before after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run sdk code before = ok (value,after)) :
    traceLog hashv impl after = traceLog hashv impl before ++
      SdkC_Source.readLog (SdkC_Source.run hashv (lower impl code) []).2 := by
  induction code generalizing before after with
  | done a =>
    cases Result.ok.inj ran
    simp only [lower,SdkC_Source.run,SdkC_Source.readLog,List.filterMap_nil,List.append_nil]
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
      have called := (law op good.1).trans actual
      simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran
      have next := ih a (good.2 a) (before ++ [.returned op a]) after ran
      obtain ⟨chosen,hchosen,_,logs⟩ := GExq_CodeTrace.success_bind hashv
        (impl op) (fun b => lower impl (k b)) value total
      have same : chosen = a := Result.ok.inj (hchosen.symm.trans called)
      subst chosen
      simp only [traceLog,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        eventLog,List.append_nil] at next
      simpa only [lower,logs,List.append_assoc,traceLog] using next

#print axioms ordered
end AspisR1.RawK_TraceLogs
end
