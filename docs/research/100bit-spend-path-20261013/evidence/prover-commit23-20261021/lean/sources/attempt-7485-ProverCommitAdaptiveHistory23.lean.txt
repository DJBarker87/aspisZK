import R1Z.ProverCommitAdaptiveLaw23
/-! Joint ordered-history law for adaptively addressed marked draws.
Supplying the marked vector independently, while memoizing it for all later
reads, preserves every rational test of the full view. This is a generic
interpreter transport, not an asserted shipped-source instance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitAdaptiveHistory23
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open R1Z.QueryScanFreshProgram R1Z.ProverCommitAdaptiveLaw23 R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable
variable {I A O : Type} [DecidableEq I] [Fintype A]

/-- Expectation with an external marked vector. All ordinary first reads
are still sampled lazily; repeated reads use the retained common table.
The observation receives the complete ordered history, including repeats. -/
def suppliedMean : {n : Nat} → Marked I A n → Table I A → Finset I →
    (Bool × (Fin n → A) → O) → (Fin n → A) → (View I A O → ℚ) → ℚ
  | _, .done, _, _, out, _, observe => observe ([],out (true,fun i => i.elim0))
  | _, .other i next, table, seen, out, coins, observe =>
      match table i with
      | some a => suppliedMean (next a) table (insert i seen) out coins
          (fun r => observe ((i,a)::r.1,r.2))
      | none => mean (fun a => suppliedMean (next a) (put table i a) (insert i seen)
          out coins (fun r => observe ((i,a)::r.1,r.2)))
  | _, .scan i next, table, seen, out, coins, observe =>
      let a := coins 0
      suppliedMean (next a) (put table i a) (insert i seen)
        (fun r => out (decide (i ∉ seen) && r.1,Fin.cons a r.2))
        (fun j => coins j.succ) (fun r => observe ((i,a)::r.1,r.2))

/-- Full joint law, not merely the marginal distribution of marked answers.
Outputs may include failure, retry/abort choices and final retained state. -/
theorem lazy_joint [Nonempty A] {n : Nat} (program : Marked I A n)
    (table : Table I A) (seen : Finset I) (consistent : Consistent table seen)
    (fresh : Fresh program seen) (out : Bool × (Fin n → A) → O)
    (observe : View I A O → ℚ) :
    lazyMean (compile program seen out) table observe =
      mean (fun coins => suppliedMean program table seen out coins observe) := by
  induction program generalizing table seen observe with
  | done =>
    exact (mean_const _).symm
  | @other n i next ih =>
    cases hi : table i with
    | some a =>
      simp only [compile,lazyMean,suppliedMean,hi]
      exact ih a table (insert i seen) (consistent_cached table seen consistent i a hi)
        (fresh a) out (fun r => observe ((i,a)::r.1,r.2))
    | none =>
      simp only [compile,lazyMean,suppliedMean,hi]
      calc _ = mean (fun a => mean (fun coins => suppliedMean (next a)
          (put table i a) (insert i seen) out coins
          (fun r => observe ((i,a)::r.1,r.2)))) := by
            apply congrArg mean
            funext a
            exact ih a (put table i a) (insert i seen)
              (consistent_put table seen consistent i a) (fresh a) out _
           _ = _ := mean_comm _
  | @scan n i next ih =>
    have hi : table i = none := (consistent i).mpr fresh.1
    simp only [compile,lazyMean,hi]
    calc _ = mean (fun a => mean (fun coins => suppliedMean (next a)
          (put table i a) (insert i seen)
          (fun r => out (decide (i ∉ seen) && r.1,Fin.cons a r.2)) coins
          (fun r => observe ((i,a)::r.1,r.2)))) := by
            apply congrArg mean
            funext a
            exact ih a (put table i a) (insert i seen)
              (consistent_put table seen consistent i a) (fresh.2 a) _ _
         _ = _ := by
            simpa only [suppliedMean,Fin.cons_zero,Fin.cons_succ] using
              (mean_cons (fun coins => suppliedMean (.scan i next) table seen out coins observe))

/-- A single uniform complete oracle and independent supplied marked draws
have equal full-view laws under the same explicit freshness invariant. -/
theorem complete_joint [Fintype I] [Nonempty A] {n : Nat}
    (program : Marked I A n) (fresh : Fresh program ∅)
    (out : Bool × (Fin n → A) → O) (observe : View I A O → ℚ) :
    mean (fun oracle : I → A => observe (eval oracle (compile program ∅ out))) =
      mean (fun coins => suppliedMean program (fun _ => none) ∅ out coins observe) :=
  (empty_oracle_law (compile program ∅ out) observe).trans
    (lazy_joint program (fun _ => none) ∅ (by intro i; simp) fresh out observe)

#print axioms lazy_joint
#print axioms complete_joint
end R1Z.ProverCommitAdaptiveHistory23
