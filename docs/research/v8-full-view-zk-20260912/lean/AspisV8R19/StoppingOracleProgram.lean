import AspisV8R19.OracleFiniteSupport

/-! A bounded causal controller with explicit stop and fuel-exhaustion
outcomes. This law retains failures; it does not condition on publication.
The controller is fixed before oracle sampling and can see only its past log. -/
set_option autoImplicit false
namespace AspisV8R19.StoppingOracleProgram
open MemoizedProgramLaw OracleFiniteSupport OracleResampling
variable {I A O : Type}

inductive Decision (I O : Type) where
  | stop (outcome : O)
  | query (input : I)
inductive Outcome (O : Type) where
  | stopped (outcome : O)
  | exhausted

def compile (policy : List (I × A) → Decision I O) :
    ℕ → List (I × A) → Program I A (Outcome O)
  | 0, history => match policy history with
      | .stop o => .done (.stopped o)
      | .query _ => .done .exhausted
  | n+1, history => match policy history with
      | .stop o => .done (.stopped o)
      | .query i => .ask i (fun a => compile policy n (history ++ [(i,a)]))

def run (policy : List (I × A) → Decision I O) (H : I → A) :
    ℕ → List (I × A) → View I A (Outcome O)
  | 0, history => match policy history with
      | .stop o => ([],.stopped o)
      | .query _ => ([],.exhausted)
  | n+1, history => match policy history with
      | .stop o => ([],.stopped o)
      | .query i =>
          let tail := run policy H n (history ++ [(i,H i)])
          ((i,H i)::tail.1,tail.2)

theorem compile_exact (policy : List (I × A) → Decision I O) (H : I → A)
    (fuel : ℕ) (history : List (I × A)) :
    eval H (compile policy fuel history) = run policy H fuel history := by
  induction fuel generalizing history with
  | zero => cases h : policy history <;> simp [compile,run,h,eval]
  | succ n ih => cases h : policy history <;> simp [compile,run,h,eval,ih]

theorem calls_bounded (policy : List (I × A) → Decision I O) (H : I → A)
    (fuel : ℕ) (history : List (I × A)) :
    (run policy H fuel history).1.length ≤ fuel := by
  induction fuel generalizing history with
  | zero => cases h : policy history <;> simp [run,h]
  | succ n ih =>
      cases h : policy history with
      | stop o => simp [run,h]
      | query i => simpa [run,h] using Nat.succ_le_succ (ih (history ++ [(i,H i)]))

theorem stopped_no_reads (policy : List (I × A) → Decision I O) (H : I → A)
    (fuel : ℕ) (history : List (I × A)) (o : O) (h : policy history = .stop o) :
    run policy H fuel history = ([],.stopped o) := by
  cases fuel <;> simp [run,h]

theorem stopped_law [Fintype A] [Nonempty A] [DecidableEq I]
    (policy : List (I × A) → Decision I O) (fuel : ℕ) (fallback : A)
    (observe : View I A (Outcome O) → ℚ) :
    let p := compile policy fuel []
    mean (fun H : {i // i ∈ support p} → A =>
      observe (run policy (extend (support p) H fallback) fuel [])) =
      lazyMean p (fun _ => none) observe := by
  dsimp only
  have h := finite_support_oracle_law (compile policy fuel []) _
    (fun _ h => h) fallback observe
  simpa only [compile_exact] using h

#print axioms compile_exact
#print axioms calls_bounded
#print axioms stopped_no_reads
#print axioms stopped_law
end AspisV8R19.StoppingOracleProgram
