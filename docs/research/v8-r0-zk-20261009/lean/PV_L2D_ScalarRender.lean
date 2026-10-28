import PV_L2D_ScalarPort
set_option autoImplicit false
namespace PV_L2D_ScalarRender
open PV_L2D_ScalarPort
variable {S C W : Type}

def render (tick : C → C) (wordTrace : C → List W) :
    Nat → Nat → C → Bool → List (Event W)
  | 0, retry, _c, success => if success then [] else [.cap retry false]
  | k+1, retry, c, success =>
    .cap retry true :: (wordTrace c).map Event.word ++
      .accept (success && decide (k=0)) :: render tick wordTrace k (retry+1) (tick c) success

theorem positive_when_running (next : S → Draw S W) (n retry : Nat) (s : S) :
    0<(sample next (n+1) retry s).consumed := by
  simp only [sample]
  split <;> simp
#print axioms positive_when_running

theorem some_positive (next : S → Draw S W) (n retry : Nat) (s : S)
    (h : (sample next n retry s).value.isSome=true) :
    0<(sample next n retry s).consumed := by
  cases n with
  | zero => simp [sample] at h
  | succ n => exact positive_when_running next n retry s
#print axioms some_positive

/-- Port hypotheses describe only the public clock and per-word trace.
They are discharged by the concrete expander, not added to T. -/
theorem trace_render (next : S → Draw S W) (clock : S → C) (tick : C → C)
    (wordTrace : C → List W)
    (step : ∀ s, clock (next s).after=tick (clock s))
    (trace : ∀ s, (next s).events=wordTrace (clock s))
    (n retry : Nat) (s : S) :
    (sample next n retry s).events = render tick wordTrace
      (sample next n retry s).consumed retry (clock s) (sample next n retry s).value.isSome := by
  induction n generalizing retry s with
  | zero => simp [sample,render]
  | succ n ih =>
    by_cases h : PV_L2B_SourceWords.candidate (next s).word<2147483647
    · simp [sample,h,render,trace]
    · have hr:=ih (retry+1) (next s).after
      have hb : ((sample next n (retry+1) (next s).after).value.isSome &&
          decide ((sample next n (retry+1) (next s).after).consumed=0))=false := by
        cases hv : (sample next n (retry+1) (next s).after).value with
        | none => simp [hv]
        | some v =>
          have hp:=some_positive next n (retry+1) (next s).after (by simp [hv])
          simp [hv,Nat.ne_of_gt hp]
      simp only [sample,h,ite_false,render,hb]
      rw [trace s,hr,step s]
      simp only [List.cons_append]
#print axioms trace_render

/-- Accepted values are absent from the rendered trace: the count and the
success/exhaustion tag determine the entire scalar branch/index sequence. -/
theorem same_count_trace (next : S → Draw S W) (clock : S → C) (tick : C → C)
    (wordTrace : C → List W)
    (step : ∀ s, clock (next s).after=tick (clock s))
    (trace : ∀ s, (next s).events=wordTrace (clock s))
    (n retry : Nat) (s t : S)
    (hc : clock s=clock t)
    (hn : (sample next n retry s).consumed=(sample next n retry t).consumed)
    (hs : (sample next n retry s).value.isSome=(sample next n retry t).value.isSome) :
    (sample next n retry s).events=(sample next n retry t).events := by
  rw [trace_render next clock tick wordTrace step trace,
    trace_render next clock tick wordTrace step trace,hc,hn,hs]
#print axioms same_count_trace
end PV_L2D_ScalarRender
