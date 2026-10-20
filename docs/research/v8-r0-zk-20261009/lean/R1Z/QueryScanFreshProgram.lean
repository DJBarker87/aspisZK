import R1Z.QueryScanIndependentHistory
import AspisV8R19.MemoizedProgramLaw

/-! Fresh marked reads of a shared memoized ROM. Unmarked reads may repeat
arbitrarily. The law is a subevent mass bound, never conditioning on an
arbitrary already revealed history. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanFreshProgram
open R0Z R0Z.FsGood R0Z.FsAbort R0Z.HvzkV
  AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
attribute [local instance] Classical.propDecidable

inductive Marked (I A : Type) : ℕ → Type
  | done : Marked I A 0
  | other {n : ℕ} (i : I) (next : A → Marked I A n) : Marked I A n
  | scan {n : ℕ} (i : I) (next : A → Marked I A n) : Marked I A (n+1)

variable {I A O : Type} [DecidableEq I]

def compile : {n : ℕ} → Marked I A n → Finset I →
    (Bool × (Fin n → A) → O) → Program I A O
  | _, .done, _, out => .done (out (true, fun i => i.elim0))
  | _, .other i next, seen, out =>
      .ask i (fun a => compile (next a) (insert i seen) out)
  | _, .scan i next, seen, out =>
      .ask i (fun a => compile (next a) (insert i seen)
        (fun r => out (decide (i ∉ seen) && r.1, Fin.cons a r.2)))

def Consistent (t : Table I A) (seen : Finset I) : Prop :=
  ∀ i, t i = none ↔ i ∉ seen

theorem consistent_put (t : Table I A) (seen : Finset I)
    (ht : Consistent t seen) (i : I) (a : A) :
    Consistent (put t i a) (insert i seen) := by
  intro j
  by_cases hj : j = i
  · subst j
    simp [put]
  · simp only [put, if_neg hj, Finset.mem_insert, not_or, hj, not_false_eq_true,
      true_and]
    exact ht j

theorem consistent_cached (t : Table I A) (seen : Finset I)
    (ht : Consistent t seen) (i : I) (a : A) (hi : t i = some a) :
    Consistent t (insert i seen) := by
  have hm : i ∈ seen := by
    by_contra hn
    have := (ht i).mpr hn
    rw [hi] at this
    contradiction
  rwa [Finset.insert_eq_of_mem hm]

/-- Fin.cons exposes precisely one independent coordinate. -/
theorem mean_cons [Fintype A] [Nonempty A] {n : ℕ} (E : (Fin (n+1) → A) → ℚ) :
    mean (fun a => mean (fun q : Fin n → A => E (Fin.cons a q))) = mean E := by
  have he := R1Z.CouplingR1PBin.mp_equiv (Fin.consEquiv (fun _ : Fin (n+1) => A)) E
  rw [LawTransport.mean_product] at he
  exact he

/-- Arbitrary nonnegative tests of fresh marked answers are dominated by
independent words. The table may contain any earlier unmarked history. -/
theorem lazy_fresh_bound [Fintype A] [Nonempty A] {n : ℕ}
    (p : Marked I A n) (t : Table I A) (seen : Finset I)
    (ht : Consistent t seen) (out : Bool × (Fin n → A) → O)
    (observe : O → ℚ) (E : (Fin n → A) → ℚ) (hE : ∀ q, 0 ≤ E q)
    (hobs : ∀ b q, observe (out (b,q)) = if b then E q else 0) :
    lazyMean (compile p seen out) t (fun r => observe r.2) ≤ mean E := by
  induction p generalizing t seen with
  | done =>
      change observe (out (true, fun i : Fin 0 => i.elim0)) ≤ mean E
      rw [hobs]
      have hc : mean E = E (fun i : Fin 0 => i.elim0) := by
        have he : E = fun _ => E (fun i : Fin 0 => i.elim0) := by
          funext q
          congr 1
          exact Subsingleton.elim _ _
        rw [he, mean_const]
      exact hc.ge
  | @other n i next ih =>
      cases hi : t i with
      | some a =>
          simp only [compile, lazyMean, hi]
          exact ih a t (insert i seen) (consistent_cached t seen ht i a hi) out E hE hobs
      | none =>
          simp only [compile, lazyMean, hi]
          calc _ ≤ mean (fun _ : A => mean E) :=
                mean_le_mean _ _ (fun a =>
                  ih a (put t i a) (insert i seen) (consistent_put t seen ht i a)
                    out E hE hobs)
               _ = mean E := mean_const _
  | @scan n i next ih =>
      cases hi : t i with
      | some a =>
          have hm : i ∈ seen := by
            by_contra hn
            have := (ht i).mpr hn
            rw [hi] at this
            contradiction
          simp only [compile, lazyMean, hi]
          have hb := ih a t (insert i seen) (consistent_cached t seen ht i a hi)
            (fun r => out (decide (i ∉ seen) && r.1, Fin.cons a r.2))
            (fun _ => 0) (fun _ => le_rfl) (by
              intro b q
              simp only [hm, not_true_eq_false, decide_false, Bool.false_and, hobs]
              cases b <;> rfl)
          rw [mean_const] at hb
          exact hb.trans (mean_nonneg _ hE)
      | none =>
          have hm : i ∉ seen := (ht i).mp hi
          simp only [compile, lazyMean, hi]
          calc _ ≤ mean (fun a => mean (fun q : Fin n → A => E (Fin.cons a q))) := by
                apply mean_le_mean
                intro a
                exact ih a (put t i a) (insert i seen) (consistent_put t seen ht i a)
                  (fun r => out (decide (i ∉ seen) && r.1, Fin.cons a r.2))
                  (fun q => E (Fin.cons a q)) (fun q => hE _) (by
                    intro b q
                    simp [hm, hobs])
               _ = mean E := mean_cons E

/-- Complete uniform ROM semantics inherit the marked-fresh subevent bound.
This reuses the existing exact memoized-oracle law, including cached reads. -/
theorem fresh_oracle_bound [Fintype I] [Fintype A] [Nonempty A] {n : ℕ}
    (p : Marked I A n) (E : (Fin n → A) → Prop) :
    mean (fun H : I → A =>
      let r := (eval H (compile p ∅ id)).2
      if r.1 = true ∧ E r.2 then (1 : ℚ) else 0) ≤ eventMass E := by
  have he := empty_oracle_law (compile p ∅ id)
    (fun v => if v.2.1 = true ∧ E v.2.2 then (1 : ℚ) else 0)
  have he' : mean (fun H : I → A =>
      let r := (eval H (compile p ∅ id)).2
      if r.1 = true ∧ E r.2 then (1 : ℚ) else 0) =
      lazyMean (compile p ∅ id) (fun _ => none)
        (fun v => if v.2.1 = true ∧ E v.2.2 then (1 : ℚ) else 0) := by
    convert he using 1 <;> congr 1 <;> funext H <;> split_ifs <;> rfl
  rw [he']
  exact lazy_fresh_bound p (fun _ => none) ∅ (by intro i; simp [Consistent]) id
    (fun r => if r.1 = true ∧ E r.2 then 1 else 0)
    (fun q => if E q then 1 else 0) (fun q => by split_ifs <;> norm_num)
    (by intro b q; cases b <;> simp)

#print axioms consistent_put
#print axioms consistent_cached
#print axioms mean_cons
#print axioms lazy_fresh_bound
#print axioms fresh_oracle_bound
end R1Z.QueryScanFreshProgram
