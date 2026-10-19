import RRProgramAbortBound
import RRProgramRecoveryContracts

noncomputable section
namespace AspisR1.RRProgramSequentialContract
open Polynomial
open AspisR1.RRProgramTraversal AspisR1.RRProgramAbortBound
open AspisR1.RRProgramRecoveryContracts AspisR1.SequentialProgramInvariants
open AspisR1.SequentialFreshProgram AspisR1.CompPolyFactorMeanTools
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
variable {I A K S : Type} [Fintype A] [Nonempty A]

/-- A single monotonically increasing tape cursor is applied around the
whole RR traversal, so different local root calls never reuse tape addresses. -/
theorem sequential_collect_abort_le (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S))))
    (mass : S → Nat) (δ : ℚ) (hδ : 0 ≤ δ)
    (hlocal : ∀ s, outMean (children s) abortIndicator ≤ (mass s : ℚ)*δ)
    (hmass : ∀ s, AllOutcomes (children s) (fun out =>
      ∀ cs, out = some cs → childMass mass cs ≤ mass s))
    (d : Nat) (s : S) (cursor : Nat) (table : Table Nat A)
    (hfuture : ∀ i, cursor ≤ i → table i = none) :
    lazyMean (sequential (collectProgram zeroTest children d s) cursor) table
      (fun v => abortIndicator v.2.1) ≤ (d : ℚ)*(mass s : ℚ)*δ := by
  rw [sequential_lazy_mean _ _ _ hfuture]
  exact collectProgram_abort_le zeroTest children mass δ hδ hlocal hmass d s

theorem sequential_collect_correct [Field K] (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S))))
    (model : S → (K[X])[X])
    (hzero : ∀ s, zeroTest s = true ↔ (model s).eval 0 = 0)
    (hchildren : ∀ s, AllOutcomes (children s) (fun out => ∀ cs, out = some cs →
      (∀ a t, (a,t) ∈ cs → ∀ f,
        (model t).eval f = 0 → (model s).eval (C a + X*f) = 0) ∧
      (∀ f, (model s).eval f = 0 → ∃ a t, (a,t) ∈ cs ∧
        a = f.coeff 0 ∧ (model t).eval f.divX = 0)))
    (d : Nat) (s : S) (cursor : Nat) :
    AllOutcomes (sequential (collectProgram zeroTest children d s) cursor)
      (fun out => ∀ candidates, out.1 = some candidates →
        CandidateResult model d s candidates) :=
  all_sequential _ _ (collectProgram_correct zeroTest children model hzero hchildren d s) cursor

#print axioms sequential_collect_abort_le
#print axioms sequential_collect_correct
end AspisR1.RRProgramSequentialContract
