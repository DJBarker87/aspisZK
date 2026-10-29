import PV_EVHD_Interface
/-! EXPERIMENTAL, NOT ADOPTED (D478). An explicit residual charge if exact
joint trace simulation cannot be established. This module never claims that
the residual is zero, negligible, or covered by an existing event. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVHD_Residual
open R0Z R0Z.FsAbort R0Z.FsStatement PV_RJ4IDB PV_EVHD_Interface
attribute [local instance] Classical.propDecidable

/-- EXPERIMENTAL: charge ONLY additional disagreement outside the old event.
This covers timing, its JSON/stdout copies, failures, order and terminals. -/
def traceResidual {S V : Type} [Fintype S] (bad : S → Prop) (real sim : S → V) : ℚ :=
  eventMass (fun s => ¬bad s ∧ real s ≠ sim s)

theorem with_residual {S V : Type} [Fintype S] (bad : S → Prop)
    (real sim : S → V) (test : V → ℚ)
    (bounded : ∀ v, 0 ≤ test v ∧ test v ≤ 1) :
    |mean (fun s => test (real s)) - mean (fun s => test (sim s))| ≤
      eventMass bad + traceResidual bad real sim := by
  have h := until_bad (fun s => test (real s)) (fun s => test (sim s))
    (fun _ => bounded _) (fun _ => bounded _)
    (fun s => bad s ∨ (¬bad s ∧ real s ≠ sim s)) (by
      intro s hs
      have hb : ¬bad s := fun h => hs (Or.inl h)
      have he : real s = sim s := Classical.byContradiction (fun h => hs (Or.inr ⟨hb,h⟩))
      exact congrArg test he)
  exact h.trans (eventMass_or_le _ _)

theorem exact_links_zero {S A Signal : Type} [Fintype S]
    (bad : S → Prop) (real sim : S → NativeTrace A) (rs ss : S → Signal)
    (context : Link_Context bad real sim) (timing : Link_Timing bad real sim)
    (signal : Link_Signal bad rs ss) :
    traceResidual bad (fun s => observe (rs s) (real s))
      (fun s => observe (ss s) (sim s)) = 0 := by
  have agree := full_agreement bad real sim rs ss context timing signal
  unfold traceResidual eventMass
  trans mean (fun _ : S => (0 : ℚ))
  · apply congrArg mean
    funext s
    apply if_neg
    rintro ⟨hb,hn⟩
    exact hn (agree s hb)
  · simp only [mean, Finset.sum_const_zero, zero_div]

/-- EXPERIMENTAL: named public-environment association. Native joint entropy
and environment marginals must be identified with the shared public product;
separate signal or clock marginal equality is insufficient. -/
def Link_PublicEnvironment {N E C : Type} [Fintype N] [Fintype E] [Fintype C]
    (actual : N → E × C) : Prop :=
  R0Z.EqualLaws actual (fun p : E × C => p)

/-- EXPERIMENTAL: native option-B signal law must be witness independent for
all equal-public witnesses. This marginal law alone never proves prefix privacy. -/
def Link_PublicSignal {W P N E Signal : Type} [Fintype N] [Fintype E]
    (pub : W → P) (p : P) (actual : W → N → Signal) (signal : E → Signal) : Prop :=
  ∀ w, pub w = p → R0Z.EqualLaws (actual w) signal

/-- EXPERIMENTAL: progressive completion cannot rewrite events already shown
to the observer. Source association and the native query schedule are still
required; this necessary prefix law does not supply those facts. -/
def Link_CausalPrefix {E V L A : Type}
    (complete : E → V → List L → NativeTrace A) : Prop :=
  ∀ e v log suffix, List.IsPrefix (complete e v log).events
    (complete e v (log ++ suffix)).events

/-- EXPERIMENTAL: exact native adaptive-program association at every
reachable source prefix. Both families range over actual invocation/prefix
indices; the expected observation is not allowed to contain future data. -/
def Link_ObserverProgram {I O : Type} (actual : I → R1Z.GamesR1.OProg)
    (expected : I → O) (program : O → R1Z.GamesR1.OProg) : Prop :=
  ∀ i, actual i = program (expected i)

/-- EXPERIMENTAL: if an exact surrogate theorem is available but the actual
joint trace differs, its additional term is explicit. No <2^-100 conclusion
is transferred without a separate bound for deltaTrace. -/
theorem headline_plus_trace {S I : Type} [Fintype S] [Fintype I]
    (actual exact : S → ℚ) (ideal : I → ℚ) (B deltaTrace : ℚ)
    (trace_link : |mean actual - mean exact| ≤ deltaTrace)
    (headline : |mean exact - mean ideal| ≤ B) :
    |mean actual - mean ideal| ≤ B + deltaTrace := by
  have h := (abs_sub_le (mean actual) (mean exact) (mean ideal)).trans
    (add_le_add trace_link headline)
  simpa only [add_comm] using h

#print axioms with_residual
#print axioms exact_links_zero
#print axioms headline_plus_trace
end PV_EVHD_Residual
