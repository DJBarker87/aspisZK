import AspisV8R19.OracleResampling
import AspisV8PairedCommitment.Table

/-! Complete-table and first-read-only semantics for finite causal programs.
The returned trace includes repeated reads. Terminal values can include every
failure, retry record and publication decision; none is conditioned away.
This is an oracle-interpreter theorem, not a source prover refinement. -/
set_option autoImplicit false
namespace AspisV8R19.MemoizedProgramLaw
open OracleResampling AspisV8PairedCommitment
variable {I A O : Type}

inductive Program (I A O : Type) where
  | done (outcome : O)
  | ask (input : I) (next : A → Program I A O)

abbrev View (I A O : Type) := List (I × A) × O

def eval (H : I → A) : Program I A O → View I A O
  | .done o => ([],o)
  | .ask i next =>
      let tail := eval H (next (H i))
      ((i,H i)::tail.1,tail.2)

def complete (t : Table I A) (H : I → A) : I → A := fun i => (t i).getD (H i)

noncomputable def lazyMean [Fintype A] [DecidableEq I] :
    Program I A O → Table I A → (View I A O → ℚ) → ℚ
  | .done o, _, observe => observe ([],o)
  | .ask i next, t, observe =>
      match t i with
      | some a => lazyMean (next a) t (fun r => observe ((i,a)::r.1,r.2))
      | none => mean (fun a => lazyMean (next a) (put t i a)
          (fun r => observe ((i,a)::r.1,r.2)))

theorem complete_empty (H : I → A) : complete (fun _ => none) H = H := rfl

theorem complete_missing (t : Table I A) (H : I → A) (i : I) (h : t i = none) :
    complete t H i = H i := by simp [complete,h]

theorem complete_cached (t : Table I A) (H : I → A) (i : I) (a : A)
    (h : t i = some a) : complete t H i = a := by simp [complete,h]

theorem complete_resample [DecidableEq I] (t : Table I A) (H : I → A)
    (i : I) (a : A) (h : t i = none) :
    complete t (Function.update H i a) = complete (put t i a) H := by
  funext j
  by_cases hj : j=i
  · subst j; simp [complete,put,h]
  · simp [complete,put,hj,Function.update_of_ne]

theorem complete_put_at [DecidableEq I] (t : Table I A) (H : I → A) (i : I) (a : A) :
    complete (put t i a) H i = a := by simp [complete,put]

theorem lazy_cached [Fintype A] [DecidableEq I] (i : I) (next : A → Program I A O)
    (t : Table I A) (a : A) (h : t i = some a) (observe : View I A O → ℚ) :
    lazyMean (.ask i next) t observe =
      lazyMean (next a) t (fun r => observe ((i,a)::r.1,r.2)) := by
  simp only [lazyMean,h]

theorem exact_oracle_law [Fintype I] [Fintype A] [Nonempty A] [DecidableEq I]
    (p : Program I A O) (t : Table I A) (observe : View I A O → ℚ) :
    mean (fun H => observe (eval (complete t H) p)) = lazyMean p t observe := by
  induction p generalizing t observe with
  | done o =>
      change mean (fun _ : I → A => observe ([],o)) = observe ([],o)
      exact mean_const _
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          rw [lazy_cached i next t a ht]
          rw [← ih a t (fun r => observe ((i,a)::r.1,r.2))]
          apply mean_congr
          intro H
          simp only [eval,complete_cached t H i a ht]
      | none =>
          rw [lazyMean,ht]
          rw [resample_cell i (fun H => observe (eval (complete t H) (.ask i next)))]
          apply mean_congr
          intro a
          rw [← ih a (put t i a) (fun r => observe ((i,a)::r.1,r.2))]
          apply mean_congr
          intro H
          rw [complete_resample t H i a ht]
          simp only [eval,complete_put_at]

theorem empty_oracle_law [Fintype I] [Fintype A] [Nonempty A] [DecidableEq I]
    (p : Program I A O) (observe : View I A O → ℚ) :
    mean (fun H => observe (eval H p)) = lazyMean p (fun _ => none) observe :=
  exact_oracle_law p (fun _ => none) observe

theorem outcome_event_law [Fintype I] [Fintype A] [Nonempty A] [DecidableEq I]
    (p : Program I A O) (event : View I A O → Prop) [DecidablePred event] :
    mean (fun H => if event (eval H p) then 1 else 0) =
      lazyMean p (fun _ => none) (fun r => if event r then 1 else 0) :=
  empty_oracle_law p (fun r => if event r then 1 else 0)

#print axioms complete_empty
#print axioms complete_missing
#print axioms complete_cached
#print axioms complete_resample
#print axioms complete_put_at
#print axioms lazy_cached
#print axioms exact_oracle_law
#print axioms empty_oracle_law
#print axioms outcome_event_law
end AspisV8R19.MemoizedProgramLaw
