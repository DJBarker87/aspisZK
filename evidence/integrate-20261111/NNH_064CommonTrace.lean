import NNH_064CommonRecords
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064CommonTrace
open Aeneas Aeneas.Std NJU_CommonObserved NLT_NativeInvocation

def trace (env : RSL.Env) (pub proof ck : Slice U8) :=
 (NKE_Free.eval (NNH_064CommonRecords.program env pub proof ck)).events.flatMap
  (NNH_064SourceDetails.trace env)

theorem decorate (env : RSL.Env) (pub proof ck : Slice U8)
 (es : List Event) (subset : ∀ e∈es,e∈(NKE_Free.eval (NNH_064CommonRecords.program env pub proof ck)).events) :
 NNC_RecordTrace.Records (es.pmap (fun e h=>NNH_064CommonRecords.record env pub proof ck e h) subset)
  (es.flatMap (NNH_064SourceDetails.trace env)) := by
 induction es with
 | nil => exact .nil
 | cons head tail ih =>
   apply NNC_RecordTrace.Records.cons
   · exact NNH_064SourceDetails.source env pub proof ck head _
   · exact ih (fun e h=>subset e (List.mem_cons_of_mem _ h))

theorem source (env : RSL.Env) (pub proof ck : Slice U8) :
 NNC_RecordTrace.Records (NNH_064CommonRecords.records env pub proof ck) (trace env pub proof ck) :=
 decorate env pub proof ck _ (fun _ h=>h)

theorem bound (env : RSL.Env) (pub proof ck : Slice U8)
 (es : List Event) (subset : ∀ e∈es,e∈(NKE_Free.eval (NNH_064CommonRecords.program env pub proof ck)).events) :
 LIBB_EnvCommon.Bound env (es.pmap (fun e h=>NNH_064CommonRecords.record env pub proof ck e h) subset) := by
 induction es with
 | nil => intro r h; cases h
 | cons head tail ih =>
   intro r member
   rcases List.mem_cons.mp member with same|member
   · subst r
     exact NNH_064SourceInputs.bound env pub proof ck head _
   · exact ih (fun e h=>subset e (List.mem_cons_of_mem _ h)) r member

#print axioms decorate
#print axioms source
#print axioms bound
end AspisR1.NNH_064CommonTrace
