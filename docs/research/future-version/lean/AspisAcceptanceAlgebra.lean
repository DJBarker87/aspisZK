import AspisPairResidualBridge

/-! The Aspis one-transaction verifier, acceptance-to-extraction link, part 1:
the algebra over fixed data.

Kind of result: MATHEMATICAL MODEL THEOREMS over R1's `MatchingSupport.Data`
(the committed words, the final message and the challenges as fixed values)
and an ordered query vector, generic in the fields `K`, `E` (kept abstract, as
R1's `HchecksAccumulator` does, to avoid normalising the concrete tower). No
probability, Fiat--Shamir, binding or source statement.

* `natVec`: a 64-entry vector as a function on `ℕ` (the final-sumcheck
  model's carrier).
* (W) `relation_sum`: the model's `∑_{j<64} f_j W_j` is R1's
  `RoundPairing.dot d.f (dualFold α1 (dualFold α0 (weights F F0 κ)))`, the
  right side of the first conjunct of `MatchingSupport.AcceptedPairing`.
* (w) `secondResidual_eq_neg`: the model's second-fold residuals are minus
  R1's `QueryResidualBridge.residuals` (via R1's `residuals_eq`).
* (sign) `bad2_neg`: the pair bad set does not see the sign of the second
  family.
* `chainBad_index`: a bad round of the six-round chain is a bad round at an
  index, with the prefix read as the earlier rounds (the per-row shape the
  classifier needs).
* `link_model`: outside the bad events of the batching challenge, the
  combining challenge and the six rounds, the batched first-fold equation and
  the final check give R1's relation equality, every per-query first-fold
  equality and every second-fold residual zero. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AspisAcceptance
open scoped BigOperators
open AspisCircleGroupOrder
open AspisR1 AspisR1.MatchingSupport
open AspisFuture.StageD
open Finset

variable {K E : Type} [Field K] [Fintype K]
  [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]

/-- A 64-entry vector as a function on `ℕ`, zero from 64 on. -/
def natVec (v : Fin 64 → E) : ℕ → E := fun j => if h : j < 64 then v ⟨j, h⟩ else 0

theorem sum_natVec (N : ℕ) (hN : N = 64) (a b : Fin 64 → E) :
    ∑ j ∈ range N, natVec a j * natVec b j = ∑ j : Fin 64, a j * b j := by
  subst hN
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [natVec]

/-- R1's folded relation weight vector (`MatchingSupport.AcceptedPairing`). -/
def relW (d : Data E) : Fin 64 → E :=
  AspisR1.RoundPairing.dualFold (n := 64) d.alpha1
    (AspisR1.RoundPairing.dualFold (n := 256) d.alpha0
      (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa))

/-- (W) The model's relation sum is R1's dot product. -/
theorem relation_sum (N : ℕ) (hN : N = 64) (d : Data E) :
    ∑ j ∈ range N, natVec d.f j * natVec (relW d) j =
      AspisR1.RoundPairing.dot d.f (relW d) := by
  rw [sum_natVec N hN]
  rfl

theorem residualPolynomial_neg (r : Fin 22 → E) :
    residualPolynomial (fun i => - r i) = - residualPolynomial r := by
  unfold residualPolynomial
  simp [map_neg, Finset.sum_neg_distrib]

/-- (sign) The pair bad set does not depend on the sign of the second family. -/
theorem bad2_neg (iota : K →+* E) (r0 r1 : Fin 22 → E) :
    bad2 iota r0 (fun i => - r1 i) = bad2 iota r0 r1 := by
  unfold bad2 rootsIn
  by_cases h0 : residualPolynomial r0 = 0
  · by_cases h1 : residualPolynomial r1 = 0
    · simp [h0, h1, residualPolynomial_neg]
    · simp only [h0, h1, residualPolynomial_neg, neg_ne_zero, ne_eq, not_true_eq_false,
        not_false_eq_true, if_false, if_true, Polynomial.eval_neg, neg_eq_zero]
      ext x
      simp
  · simp [h0]

/-- A bad round of the chain is a bad round at an index `b`, whose bad set is
read from the first `b` rounds (folded vectors and running claim). -/
theorem chainBad_index (iota : K →+* E) :
    ∀ (xs : List (K × E × E)) (f u : ℕ → E) (cl : E),
      chainBad iota xs f u cl →
      ∃ b, ∃ hb : b < xs.length,
        (xs[b]'hb).1 ∈ roundBad iota
          (roundPoly (2 ^ (xs.length - b - 1))
            (foldAll iota ((xs.take b).map Prod.fst) f)
            (foldAll iota ((xs.take b).map Prod.fst) u))
          (finalClaim iota (xs.take b) cl) (xs[b]'hb).2.1 (xs[b]'hb).2.2
  | [], _, _, _, h => absurd h (by simp [chainBad])
  | x :: xs, f, u, cl, h => by
    simp only [chainBad] at h
    rcases h with h | h
    · refine ⟨0, by simp, ?_⟩
      simpa [foldAll, finalClaim] using h
    · obtain ⟨b, hb, hbad⟩ := chainBad_index iota xs _ _ _ h
      refine ⟨b + 1, by simp; omega, ?_⟩
      have hlen : (x :: xs).length - (b + 1) - 1 = xs.length - b - 1 := by simp
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, foldAll,
        finalClaim, hlen]
      exact hbad

/-- The converse: no bad round at any index means no chain hit. -/
theorem not_chainBad_of_index (iota : K →+* E) (xs : List (K × E × E)) (f u : ℕ → E) (cl : E)
    (h : ∀ b (hb : b < xs.length),
      (xs[b]'hb).1 ∉ roundBad iota
        (roundPoly (2 ^ (xs.length - b - 1))
          (foldAll iota ((xs.take b).map Prod.fst) f)
          (foldAll iota ((xs.take b).map Prod.fst) u))
        (finalClaim iota (xs.take b) cl) (xs[b]'hb).2.1 (xs[b]'hb).2.2) :
    ¬ chainBad iota xs f u cl := by
  intro hc
  obtain ⟨b, hb, hbad⟩ := chainBad_index iota xs f u cl hc
  exact h b hb hbad

variable [Algebra (ZMod P) K]

/-- The basis values of the query nodes as functions on `ℕ`. -/
def basisE (iota : K →+* E) (q : Fin 22 → Fin 262144) : Fin 22 → ℕ → E :=
  fun i j => if h : j < 64 then iota (QueryResidualBridge.basis (K := K) q i ⟨j, h⟩) else 0

/-- (w) The model's second-fold residuals are minus R1's residuals. -/
theorem secondResidual_eq_neg (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144)
    (N : ℕ) (hN : N = 64) :
    secondResidual N (natVec d.f) (basisE iota q) (QueryResidualBridge.values d q) =
      fun i => - QueryResidualBridge.residuals d q i := by
  subst hN
  funext i
  rw [QueryResidualBridge.residuals_eq iota d q]
  unfold secondResidual ResidualBatch.residual
  rw [Finset.sum_range]
  have hterm : ∀ j : Fin 64, natVec d.f (j : ℕ) * basisE iota q i (j : ℕ) =
      d.f j * iota (QueryResidualBridge.basis (K := K) q i j) := by
    intro j
    simp [natVec, basisE]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  ring

/-- `rhs2` as the model computes it. -/
theorem rhs2Of_values (iota : K →+* E) (rho : K) (d : Data E) (q : Fin 22 → Fin 262144) :
    rhs2Of iota rho (QueryResidualBridge.values d q) =
      ∑ i : Fin 22, (iota rho) ^ i.val * QueryResidualBridge.values d q i := rfl

/-! Generic packaging of the quantities the concrete transcript layer reads,
so that concrete statements are instances of these definitions and never
re-elaborate field arithmetic over the concrete tower (as R1's
`HchecksAccumulator` does). -/

/-- The true relation sum `S_W`. -/
def SWg (d : Data E) : E := ∑ j ∈ range 64, natVec d.f j * natVec (relW d) j

/-- The true query-weight sum `S_w`. -/
def Swg (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) (rho : K) : E :=
  ∑ j ∈ range 64, natVec d.f j * qweight iota rho (basisE iota q) j

/-- The combined vector `u = W + λ w`. -/
def uvecg (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) (rho lam : K) : ℕ → E :=
  fun j => natVec (relW d) j + iota lam * qweight iota rho (basisE iota q) j

/-- The initial claim `C_0 = claim + λ rhs2`. -/
def claim0 (iota : K →+* E) (claimS rhs2 : E) (lam : K) : E := claimS + iota lam * rhs2

/-- The combining-challenge bad set read from `(d, q, ρ)` and the row-33 message. -/
def lamBadSet (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) (rho : K)
    (claimS rhs2 : E) : Finset K :=
  lambdaBad iota (SWg d - claimS) (Swg iota d q rho - rhs2)

/-- The bad set of round `b` read from the earlier rounds `pre` and the row's
message `(c0, c2)`. -/
def roundBadSet (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) (rho lam : K)
    (claimS rhs2 : E) (b : ℕ) (pre : List (K × E × E)) (c0 c2 : E) : Finset K :=
  roundBad iota
    (roundPoly (2 ^ (6 - b - 1))
      (foldAll iota (pre.map Prod.fst) (natVec d.f))
      (foldAll iota (pre.map Prod.fst) (uvecg iota d q rho lam)))
    (finalClaim iota pre (claim0 iota claimS rhs2 lam)) c0 c2

/-- The batched first-fold equation. -/
def FirstBatch (iota : K →+* E) (rho : K) (d : Data E) (q : Fin 22 → Fin 262144) : Prop :=
  ∑ i : Fin 22, (iota rho) ^ i.val * AspisPairResidual.firstResiduals d q i = 0

/-- The final check `C_6 = f~(r) (W~(r) + λ w~(r))`. -/
def FinalCheck (iota : K →+* E) (rounds : List (K × E × E)) (claimS rhs2 : E) (lam rho : K)
    (d : Data E) (q : Fin 22 → Fin 262144) : Prop :=
  finalClaim iota rounds (claim0 iota claimS rhs2 lam) =
    foldAll iota (rounds.map Prod.fst) (natVec d.f) 0 *
      (foldAll iota (rounds.map Prod.fst) (natVec (relW d)) 0 +
        iota lam * foldAll iota (rounds.map Prod.fst) (qweight iota rho (basisE iota q)) 0)

/-- No bad round at any index (with six rounds) means no chain hit. -/
theorem rounds_ok (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) (rho lam : K)
    (claimS rhs2 : E) (rounds : List (K × E × E)) (h6 : rounds.length = 6)
    (h : ∀ b (hb : b < rounds.length),
      (rounds[b]'hb).1 ∉ roundBadSet iota d q rho lam claimS rhs2 b (rounds.take b)
        (rounds[b]'hb).2.1 (rounds[b]'hb).2.2) :
    ¬ chainBad iota rounds (natVec d.f) (uvecg iota d q rho lam) (claim0 iota claimS rhs2 lam) := by
  apply not_chainBad_of_index
  intro b hb
  have hb' := h b hb
  unfold roundBadSet at hb'
  rw [h6]
  exact hb'

/-- The model link: outside the three families of bad events the batched
first-fold equation and the final check give R1's relation equality, every
per-query first-fold equality, and every second-fold residual zero. -/
theorem link_model (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144)
    (rho lam : K) (claimS : E) (rounds : List (K × E × E)) (h6 : rounds.length = 6)
    (hfirst : FirstBatch iota rho d q)
    (hfinal : FinalCheck iota rounds claimS (rhs2Of iota rho (QueryResidualBridge.values d q))
      lam rho d q)
    (hrho : rho ∉ AspisPairResidual.pairBad iota d q)
    (hlam : lam ∉ lamBadSet iota d q rho claimS (rhs2Of iota rho (QueryResidualBridge.values d q)))
    (hrounds : ∀ b (hb : b < rounds.length),
      (rounds[b]'hb).1 ∉ roundBadSet iota d q rho lam claimS
        (rhs2Of iota rho (QueryResidualBridge.values d q)) b (rounds.take b)
        (rounds[b]'hb).2.1 (rounds[b]'hb).2.2) :
    AspisR1.RoundPairing.dot d.f (relW d) = claimS ∧
      (∀ i, match0 d (q i)) ∧
      (∀ i, QueryResidualBridge.residuals d q i = 0) := by
  have hN : 2 ^ rounds.length = 64 := by rw [h6]; norm_num
  have hrho' : rho ∉ bad2 iota (AspisPairResidual.firstResiduals d q)
      (secondResidual (2 ^ rounds.length) (natVec d.f) (basisE iota q)
        (QueryResidualBridge.values d q)) := by
    rw [secondResidual_eq_neg iota d q _ hN, bad2_neg]
    exact hrho
  have hlam' : lam ∉ lambdaBad iota
      ((∑ j ∈ range (2 ^ rounds.length), natVec d.f j * natVec (relW d) j) - claimS)
      ((∑ j ∈ range (2 ^ rounds.length), natVec d.f j * qweight iota rho (basisE iota q) j) -
        rhs2Of iota rho (QueryResidualBridge.values d q)) := by
    rw [hN]
    exact hlam
  have hrounds' := rounds_ok iota d q rho lam claimS _ rounds h6 hrounds
  have hmain := stageCD_sound iota rounds (natVec d.f) (natVec (relW d)) (basisE iota q)
    (QueryResidualBridge.values d q) (AspisPairResidual.firstResiduals d q) claimS rho lam
    hfirst hfinal hrho' hlam' hrounds'
  obtain ⟨hW, _, h0, h1⟩ := hmain
  refine ⟨?_, ?_, ?_⟩
  · rw [← relation_sum (2 ^ rounds.length) hN d]
    exact hW
  · intro i
    exact (AspisPairResidual.firstResidual_eq_zero_iff d q i).mp (h0 i)
  · intro i
    have h := h1 i
    rw [secondResidual_eq_neg iota d q _ hN] at h
    exact neg_eq_zero.mp h

#print axioms relation_sum
#print axioms bad2_neg
#print axioms chainBad_index
#print axioms not_chainBad_of_index
#print axioms secondResidual_eq_neg
#print axioms rounds_ok
#print axioms link_model
end AspisAcceptance
end
