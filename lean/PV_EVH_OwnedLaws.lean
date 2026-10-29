import PV_EVH_Residual
/-! D508 owned algebra. These implications do not install a deployed producer,
assume bounded native noise, or replace a source-independence proof. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OwnedLaws
open R0Z PV_RJ4IDB PV_EVH_Residual

/-- Extend the progressive-completion obligation one emitted answer at a time.
The single-step source law remains an explicit native obligation. -/
theorem causal_of_step {E V L A : Type}
    (complete : E → V → List L → NativeTrace A)
    (step : ∀ e v history answer, List.IsPrefix (complete e v history).events
      (complete e v (history ++ [answer])).events) : Link_CausalPrefix complete := by
  intro e v history suffix
  induction suffix generalizing history with
  | nil => exact ⟨[], List.append_nil _⟩
  | cons answer suffix ih =>
    have h := (step e v history answer).trans (ih (history ++ [answer]))
    simpa only [List.append_assoc, List.singleton_append] using h

/-- Product-law structure only. A native acquisition bijection is NOT supplied;
no claim that an OS noise variable is finite uniform is made. -/
theorem environment_of_equiv {N E C : Type} [Fintype N] [Fintype E] [Fintype C]
    (actual : N → E × C) (split : N ≃ E × C)
    (source : ∀ n, actual n = split n) : Link_PublicEnvironment actual := by
  classical
  intro value
  unfold law
  rw [FsAbort.mean_equiv split]
  apply congrArg mean
  funext pair
  rw [source, split.apply_symm_apply]

/-- Arbitrary joint observables factor through the identified product law.
This proves the averaging structure, not the native acquisition identification. -/
theorem product_expectation {N E C : Type} [Fintype N] [Fintype E] [Fintype C]
    (actual : N → E × C) (joint : Link_PublicEnvironment actual)
    (test : E × C → ℚ) :
    mean (fun n => test (actual n)) = mean (fun e => mean (fun c => test (e,c))) := by
  exact (LawTransport.mean_eq_of_equalLaws actual (fun p => p) test joint).trans
    (LawTransport.mean_product test)

/-- V400 follows from an ALL-path public signal factorization and the JOINT
acquisition law. Good-sample SignalAgreement alone is insufficient. -/
theorem public_signal_of_factorization {N E C W P Signal : Type}
    [Fintype N] [Fintype E] [Fintype C]
    (actual : N → E × C) (joint : Link_PublicEnvironment actual)
    (pub : W → P) (p : P) (signal : W → N → Signal) (publicSignal : E → Signal)
    (source : ∀ w, pub w = p → ∀ n, signal w n = publicSignal (actual n).1) :
    Link_PublicSignal pub p signal (fun pair : E × C => publicSignal pair.1) := by
  classical
  intro w hw value
  unfold law
  have transport := LawTransport.mean_eq_of_equalLaws actual (fun pair => pair)
    (fun pair : E × C => if publicSignal pair.1 = value then (1 : ℚ) else 0) joint
  convert transport using 1 <;> apply congrArg mean <;> funext n
  · rw [source w hw n]
  · rfl

/-- A precise representability obstruction: finite native carriers cannot
model an unbounded Nat-valued environmental read exactly. No native bound is
assumed or inferred; a more general probability carrier would be required. -/
theorem finite_environment_bounded {N : Type} [Fintype N] (read : N → Nat) :
    ∃ bound, ∀ n, read n ≤ bound := by
  exact ⟨Finset.univ.sup read, fun n => Finset.le_sup (Finset.mem_univ n)⟩

theorem no_unbounded_environment {N : Type} [Fintype N] (read : N → Nat)
    (unbounded : ∀ bound, ∃ n, bound < read n) : False := by
  obtain ⟨bound, bounded⟩ := finite_environment_bounded read
  obtain ⟨n, hn⟩ := unbounded bound
  exact (Nat.not_lt_of_ge (bounded n)) hn

#print axioms causal_of_step
#print axioms environment_of_equiv
#print axioms product_expectation
#print axioms public_signal_of_factorization
#print axioms finite_environment_bounded
#print axioms no_unbounded_environment
end PV_EVH_OwnedLaws
