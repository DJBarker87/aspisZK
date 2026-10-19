import R1RhoSamplerBound

/-! If a query misses the fixed two-fold matching support, the accepted
field-level query checks can pass only on the counted rho exception. This
is a final-row implication and independent-answer density result, not a
shared-oracle Fiat--Shamir or Rust-source theorem. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.RhoAcceptance

open scoped BigOperators
open AspisCircleGroupOrder AspisR1.MatchingSupport
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisR1.QueryResidualBridge

variable {A K E : Type} [Fintype A] [Field K] [Fintype K]
  [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) K] [Algebra (ZMod P) E]

def AcceptedQueries (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K) : Prop :=
  (∀ i, match0 d (q i)) ∧
    (∑ j : Fin 64, d.f j *
      iota (∑ i : Fin 22, rho ^ i.val * basis (K := K) q i j)) =
    ∑ i : Fin 22, (iota rho) ^ i.val * values d q i

theorem accepted_mem_bad_of_query_miss (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hmiss : ∃ i, q i ∉ matchingSet d)
    (haccepted : AcceptedQueries iota d q rho) : rho ∈ rhoBad iota d q := by
  classical
  by_contra hrho
  have hall := queries_match iota d q rho hrho haccepted.1
    (accumulated_equation_implies_residual_batch iota d q rho haccepted.2)
  obtain ⟨i, hi⟩ := hmiss
  exact hi (hall i)

/-- The final-row acceptance probability is bounded from actual modulo
fiber counts, for any fixed queries that miss the matching support. -/
theorem modulo_acceptance_mass_of_query_miss {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ K)
    (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144)
    (hmiss : ∃ i, q i ∉ matchingSet d) :
    mean (fun a : A => indicator (AcceptedQueries iota d q
      (output (R0C.ModuloCounting.reduce hn (input a))))) ≤
      21 * (((B / n + 1 : Nat) : ℚ) / B) := by
  apply le_trans _ (AspisR1.RhoSamplerBound.modulo_bad_mass
    hn input output iota d q)
  apply FS.mean_mono
  intro a
  exact FS.indicator_mono
    (accepted_mem_bad_of_query_miss iota d q _ hmiss)

#print axioms accepted_mem_bad_of_query_miss
#print axioms modulo_acceptance_mass_of_query_miss

end AspisR1.RhoAcceptance
end
