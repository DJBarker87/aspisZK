import AspisPairResidualBridge
import OraclePortSelectedObservationsC6

/-! The Aspis residual pair is a function of R1's per-query observation
record, so it is carried by R1's own transport from opening-derived words to
cut-recovered committed words.

Kind of result: MODEL THEOREMS over R1's matching-support data. They say: the
pair of residual vectors `(F_i - b_i, e_i - G_i)` reads the words only at
(1) the initial-word fibres of the queried positions (C1 and C2 lanes),
(2) the folded word at the queried positions, and (3) the folded fibres of
their parents -- exactly the three agreement premises of R1's
`OraclePortSelectedObservationsC6.observe_withWords`, which R1 discharges for
all three trees in `OraclePortRecoveredAcceptanceC6.accepted_checks` from
`OraclePortAllSelectedRecoveryC6.authenticated` (kind 0 = C1, 1 = C2,
2 = folded) under the one binary collision event. No probability or source
statement is made here. -/

set_option autoImplicit false
noncomputable section
namespace AspisPairResidual

open scoped BigOperators
open AspisCircleGroupOrder
open AspisR1 AspisR1.MatchingSupport AspisR1.OraclePortSelectedObservationsC6
open AspisR1.OraclePortSelectedArithmeticC4 (withWords)
attribute [local irreducible] FirstFold.foldWord TwoFoldExtraction.batchedWord
  QueryResidualBridge.values ConcreteProjection.secondEncoder

/-- The residual pair computed from an observation record. -/
def pairOf (o : Observation) (q : Fin 22 → Fin 262144) :
    (Fin 22 → AspisWideTower.WideExact) × (Fin 22 → AspisWideTower.WideExact) :=
  (fun j => o.first j - o.opened j,
   fun j => o.second j -
     AspisR1.ConcreteProjection.secondEncoder o.scalars.f (AspisR1.parentIndex (q j)))

theorem pair_eq_pairOf (d : Data AspisWideTower.WideExact) (q : Fin 22 → Fin 262144) :
    (firstResiduals d q, QueryResidualBridge.residuals d q) = pairOf (observe d q) q := by
  unfold pairOf observe firstResiduals QueryResidualBridge.residuals withWords
  rfl

/-- Replacing the words by any words that agree on the selected initial
fibres, the selected folded values and the selected folded fibres changes
neither residual vector. -/
theorem pair_withWords (d : Data AspisWideTower.WideExact)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord AspisWideTower.WideExact)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord AspisWideTower.WideExact) (q : Fin 22 → Fin 262144)
    (initial : ∀ j lane, FirstFold.fibre (d.W lane) (q j) = FirstFold.fibre (W lane) (q j))
    (opened : ∀ j, d.V (q j) = V (q j))
    (folded : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) :
    firstResiduals d q = firstResiduals (withWords d W V) q ∧
      QueryResidualBridge.residuals d q = QueryResidualBridge.residuals (withWords d W V) q := by
  have same := observe_withWords d W V q initial opened folded
  have h : (firstResiduals d q, QueryResidualBridge.residuals d q) =
      (firstResiduals (withWords d W V) q,
        QueryResidualBridge.residuals (withWords d W V) q) := by
    rw [pair_eq_pairOf, pair_eq_pairOf, same]
  exact Prod.ext_iff.mp h

variable {K : Type} [Field K] [Fintype K]

/-- The bad set of the pair is the same for both word choices. -/
theorem pairBad_withWords (iota : K →+* AspisWideTower.WideExact)
    (d : Data AspisWideTower.WideExact)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord AspisWideTower.WideExact)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord AspisWideTower.WideExact) (q : Fin 22 → Fin 262144)
    (initial : ∀ j lane, FirstFold.fibre (d.W lane) (q j) = FirstFold.fibre (W lane) (q j))
    (opened : ∀ j, d.V (q j) = V (q j))
    (folded : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) :
    pairBad iota d q = pairBad iota (withWords d W V) q := by
  obtain ⟨h0, h1⟩ := pair_withWords d W V q initial opened folded
  unfold pairBad
  rw [h0, h1]

/-- Transport of the Aspis acceptance facts. Both batched equalities, stated
for the words read from the openings (`d`), hold for the committed words
(`withWords d W V`); with the batching challenge outside the pair set of the
committed words, R1's per-query first-fold equality and residual-batch
equation hold for the committed words. -/
theorem transport_pair (iota : K →+* AspisWideTower.WideExact)
    (d : Data AspisWideTower.WideExact)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord AspisWideTower.WideExact)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord AspisWideTower.WideExact) (q : Fin 22 → Fin 262144) (rho : K)
    (initial : ∀ j lane, FirstFold.fibre (d.W lane) (q j) = FirstFold.fibre (W lane) (q j))
    (opened : ∀ j, d.V (q j) = V (q j))
    (folded : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot))
    (hrho : rho ∉ pairBad iota (withWords d W V) q)
    (h0 : ∑ i : Fin 22, (iota rho) ^ i.val * firstResiduals d q i = 0)
    (h1 : ∑ i : Fin 22, (iota rho) ^ i.val * QueryResidualBridge.residuals d q i = 0) :
    (∀ i, match0 (withWords d W V) (q i)) ∧
      (∀ i, QueryResidualBridge.residuals (withWords d W V) q i = 0) := by
  obtain ⟨e0, e1⟩ := pair_withWords d W V q initial opened folded
  rw [e0] at h0
  rw [e1] at h1
  exact pair_all_zero iota (withWords d W V) q rho hrho h0 h1

#print axioms pair_eq_pairOf
#print axioms pair_withWords
#print axioms pairBad_withWords
#print axioms transport_pair

end AspisPairResidual
end
