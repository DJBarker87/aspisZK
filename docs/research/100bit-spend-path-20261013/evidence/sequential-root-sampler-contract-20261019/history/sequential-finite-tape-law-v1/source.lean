import SequentialProgramInvariants
import AspisV8R19.OracleFiniteSupport

noncomputable section
namespace AspisR1.SequentialFiniteTapeLaw
open AspisR1.SequentialFreshProgram AspisR1.SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.OracleFiniteSupport AspisV8PairedCommitment
variable {I A O : Type} [Fintype A] [Nonempty A]

/-- A final-cursor bound applies to every potentially queried address, not
just the realized branch. Potential support is used only in this proof. -/
theorem sequential_support_below (p : Program I A O) (cursor bound : Nat)
    (hend : AllOutcomes (sequential p cursor) (fun out => out.2 ≤ bound)) :
    support (sequential p cursor) ⊆ Finset.range bound := by
  induction p generalizing cursor with
  | done o => simp only [sequential, support, Finset.empty_subset]
  | ask i next ih =>
    intro j hj
    simp only [sequential, support, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at hj
    rcases hj with rfl | ⟨a,ha⟩
    · let a : A := Classical.choice (inferInstance : Nonempty A)
      have hc := all_eval (fun _ : Nat => a) (sequential (next a) (cursor+1))
        (fun out => out.2 ≤ bound) (hend a)
      have he := sequential_eval_cursor (fun _ : Nat => a) (next a) (cursor+1)
      rw [he] at hc
      exact Finset.mem_range.mpr (by omega)
    · exact ih a (cursor+1) (hend a) ha

/-- A bounded sequential sampler has exactly the finite uniform-tape law.
The proof reuses the existing finite-support random-oracle theorem; no
uniform distribution over infinitely many addresses is postulated. -/
theorem sequential_finite_tape_law (p : Program I A O) (cursor bound : Nat)
    (hend : AllOutcomes (sequential p cursor) (fun out => out.2 ≤ bound))
    (fallback : A) (observe : O × Nat → ℚ) :
    mean (fun H : {i : Nat // i ∈ Finset.range bound} → A =>
      observe (eval (extend (Finset.range bound) H fallback) (sequential p cursor)).2) =
      lazyMean (sequential p cursor) (fun _ => none) (fun v => observe v.2) :=
  finite_support_oracle_law (sequential p cursor) (Finset.range bound)
    (sequential_support_below p cursor bound hend) fallback (fun v => observe v.2)

#print axioms sequential_support_below
#print axioms sequential_finite_tape_law
end AspisR1.SequentialFiniteTapeLaw
