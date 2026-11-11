import AspisRowDensityGeneric
import R1SelectedChallengeMap
import R1RhoSamplerBound
import AspisFinalSumcheckModel

/-! Aspis per-step accounting, row densities: the K-valued challenge sampler.

Kind of result: theorems in R1's sampler setting. The challenge of a row
`n ≥ 32` of R1's selected challenge map is `SelectedChallengeMap.sigma n s`
for a fresh duplex block `s : State`; its K-part (`rhoOf`) is
`R0P.SemSource.qm31Sample s`, R1's model of `qm31_sample` (rank of the block
modulo P^4). This is the sampler R1's row 32 (the batching challenge) uses,
and the one the Aspis combining challenge (row 33) and round challenges
(rows 34 to 39) use (`Transcript::scalar_k`). R1 defines `sigma` for every
row index; rows 33 to 39 are not rows of R1's 33-row literal transcript.

Contents.
* `perElem`, `capLambda`, `capRound`, `capPair`: exact rationals; their order,
  `capPair = RhoSamplerBound.rhoCap` (R1's row-32 budget) and closed numeric
  bounds.
* `qm31_set_mass`: for any finite `S ⊆ K`, mass of `qm31Sample s ∈ S` is at
  most `|S| * perElem`.
* `modulo_bad_mass_recovered`: R1's `RhoSamplerBound.modulo_bad_mass`,
  re-derived from the generic lemma (a check against a proved statement).
* `setBad`: R1's row-32 event shape (`LiteralRhoDensity.bad`) with the read
  and the bad set abstract: a read `read : C → Option X` of a context fixed
  before the challenge, and a bad set `S : X → Finset K`.
* `row_mean` (cap `k * perElem`) and its three instances `combining_mean`
  (`|S| ≤ 1`, `capLambda`), `round_mean` (`|S| ≤ 2`, `capRound`) and
  `pair_mean` (`|S| ≤ 21`, `capPair`), with the bad set an abstract parameter.
* `combining_mean_model`, `round_mean_model`, `pair_mean_model`: the same with
  the bad sets of the Aspis model (`AspisFuture.StageD.lambdaBad`, `roundBad`,
  `bad2`), the cardinality discharged by the model's theorems.

What these are not: no statement here says that the Aspis transcript's
prefix determines the model's quantities, that the Rust `qm31_sample`
computes `qm31Sample` (R1's open byte/field correspondence), or that the
40-row protocol instance exists. -/

set_option autoImplicit false
noncomputable section

namespace AspisRowDensity.QM31

open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep AspisCircleGroupOrder AspisWideTower
open AspisR1

abbrev K := AspisV8R15.ExactTowerBase.QM31Exact
abbrev E := WideExact
/-- The embedding R1 uses at row 32 (`LiteralOpeningView.eK`, same term). -/
abbrev eK : K →+* E := algebraMap K E

/-! ## Caps -/

/-- Per-element mass of the reduced block, `(⌊2^256 / P^4⌋ + 1) / 2^256`;
the per-element factor of `RhoSamplerBound.rhoCap`. -/
def perElem : ℚ := ((2^256 / P^4 + 1 : Nat) : ℚ) / (2^256 : Nat)

/-- Cap of the combining challenge (bad set of size at most 1). -/
def capLambda : ℚ := 1 * perElem
/-- Cap of one round challenge (bad set of size at most 2). -/
def capRound : ℚ := 2 * perElem
/-- Cap of the batching challenge for the residual pair (size at most 21). -/
def capPair : ℚ := 21 * perElem

theorem perElem_nonneg : 0 ≤ perElem :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem capPair_eq_rhoCap : capPair = RhoSamplerBound.rhoCap := rfl

/-- The exact value: `⌊2^256 / P^4⌋ = 5444517880876220229045745149051146347264`. -/
theorem perElem_eq :
    perElem = 5444517880876220229045745149051146347265 / (2^256 : ℚ) := by
  norm_num [perElem, P]

theorem capLambda_eq :
    capLambda = 5444517880876220229045745149051146347265 / (2^256 : ℚ) := by
  rw [capLambda, perElem_eq, one_mul]

theorem capRound_eq :
    capRound = 2 * 5444517880876220229045745149051146347265 / (2^256 : ℚ) := by
  rw [capRound, perElem_eq, mul_div_assoc]

theorem capPair_eq :
    capPair = 21 * 5444517880876220229045745149051146347265 / (2^256 : ℚ) := by
  rw [capPair, perElem_eq, mul_div_assoc]

theorem perElem_le_slack : perElem ≤ 1 / (P^4 : ℚ) + 1 / (2^256 : ℚ) := by
  have h := R0C.ModuloCounting.quotient_bound (2^256) (P^4) (by positivity)
    (by norm_num [P])
  simpa only [perElem, Nat.cast_pow, Nat.cast_ofNat] using h

theorem two_neg_124_lt_perElem : 1 / (2^124 : ℚ) < perElem := by
  rw [perElem_eq]; norm_num

theorem capLambda_lt : capLambda < 1 / (2^123 : ℚ) := by
  rw [capLambda_eq]; norm_num

theorem capRound_lt : capRound < 1 / (2^122 : ℚ) := by
  rw [capRound_eq]; norm_num

theorem capPair_lt : capPair < 1 / (2^119 : ℚ) := by
  rw [capPair_eq_rhoCap]; exact RhoSamplerBound.rhoCap_lt_two_neg_119

theorem capLambda_le_capRound : capLambda ≤ capRound := by
  unfold capLambda capRound; nlinarith [perElem_nonneg]

theorem capRound_le_capPair : capRound ≤ capPair := by
  unfold capRound capPair; nlinarith [perElem_nonneg]

/-- Each new cap is at most R1's row-32 budget `RhoSamplerBound.rhoCap`
(`LiteralClassifier.budget 32` is `rhoCap` by definition). -/
theorem capLambda_le_rhoCap : capLambda ≤ RhoSamplerBound.rhoCap :=
  capLambda_le_capRound.trans (capRound_le_capPair.trans (le_of_eq capPair_eq_rhoCap))

theorem capRound_le_rhoCap : capRound ≤ RhoSamplerBound.rhoCap :=
  capRound_le_capPair.trans (le_of_eq capPair_eq_rhoCap)

theorem capPair_le_rhoCap : capPair ≤ RhoSamplerBound.rhoCap :=
  le_of_eq capPair_eq_rhoCap

/-! ## The sampler mass of a set -/

/-- For any finite set `S` of `K`, the mass of `qm31Sample s ∈ S` over a
fresh block is at most `|S| * perElem`. -/
theorem qm31_set_mass (S : Finset K) :
    mean (fun s : State => indicator (R0P.SemSource.qm31Sample s ∈ S)) ≤
      (S.card : ℚ) * perElem := by
  have h := Generic.modulo_set_mass (by norm_num [P] : 0 < P^4)
    SelectedSamplerRanks.stateRank R0P.SemSource.qm31Rank S
  simp only [SelectedSamplerRanks.qm31_eq] at h
  exact h

theorem qm31_set_mass_le (S : Finset K) (k : Nat) (hS : S.card ≤ k) :
    mean (fun s : State => indicator (R0P.SemSource.qm31Sample s ∈ S)) ≤
      (k : ℚ) * perElem := by
  apply (qm31_set_mass S).trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hS
  · exact perElem_nonneg

/-- R1's `RhoSamplerBound.modulo_bad_mass`, same statement, re-derived from
the generic set lemma and R1's `QueryResidualBridge.rhoBad_card`. -/
theorem modulo_bad_mass_recovered {A K' E' : Type} [Fintype A] [Field K'] [Fintype K']
    [Field E'] [Fintype E'] [DecidableEq E'] [Algebra (ZMod P) E']
    {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ K')
    (iota : K' →+* E') (d : MatchingSupport.Data E') (q : Fin 22 → Fin 262144) :
    mean (fun a : A => indicator
      (output (R0C.ModuloCounting.reduce hn (input a)) ∈
        QueryResidualBridge.rhoBad iota d q)) ≤
      21 * (((B / n + 1 : Nat) : ℚ) / B) := by
  have h := Generic.modulo_set_mass_le hn input output
    (QueryResidualBridge.rhoBad iota d q) 21 (QueryResidualBridge.rhoBad_card iota d q)
  exact_mod_cast h

/-- On every row index `n ≥ 32`, the K-part of R1's selected challenge is
`qm31Sample`. (Rows 27 to 31 are the opening and query rows.) -/
theorem sigma_rho_of_ge (n : Nat) (hn : 32 ≤ n) (s : State) :
    SelectedChallengeMap.rhoOf (SelectedChallengeMap.sigma n s) =
      R0P.SemSource.qm31Sample s := by
  have h27 : n ≠ 27 := by omega
  have hopen : ¬ (n = 28 ∨ n = 29 ∨ n = 30) := by omega
  have h31 : n ≠ 31 := by omega
  simp only [SelectedChallengeMap.sigma, if_neg h27, if_neg hopen, if_neg h31]
  exact SelectedChallengeMap.semChal_re s

/-! ## The row event, with an abstract read and bad set -/

/-- R1's row-32 event shape (`LiteralRhoDensity.bad`): read the data the bad
set needs from a context `c` that is fixed before the challenge (`none`: no
bad challenge), then test the challenge's K-part against the set. -/
def setBad {C X : Type} (read : C → Option X) (S : X → Finset K) (c : C) (v : E) : Prop :=
  match read c with
  | none => False
  | some x => SelectedChallengeMap.rhoOf v ∈ S x

/-- The row event of `setBad` as a set: `setBad read S c v ↔ rhoOf v ∈ setOf read S c`. -/
def setOf {C X : Type} (read : C → Option X) (S : X → Finset K) (c : C) : Finset K :=
  match read c with
  | none => ∅
  | some x => S x

theorem setBad_iff {C X : Type} (read : C → Option X) (S : X → Finset K) (c : C) (v : E) :
    setBad read S c v ↔ SelectedChallengeMap.rhoOf v ∈ setOf read S c := by
  unfold setBad setOf
  cases read c with
  | none => simp
  | some x => exact Iff.rfl

theorem setOf_card {C X : Type} (read : C → Option X) (S : X → Finset K) (k : Nat)
    (hS : ∀ x, (S x).card ≤ k) (c : C) : (setOf read S c).card ≤ k := by
  unfold setOf
  cases read c with
  | none => simp
  | some x => exact hS x

/-- Generic row density: the bad set has at most `k` elements for every value
of the read. Shape of R1's `LiteralRhoDensity.rho_mean`, for any row `n ≥ 32`. -/
theorem row_mean {C X : Type} (read : C → Option X) (S : X → Finset K) (k : Nat)
    (hS : ∀ x, (S x).card ≤ k) (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read S c (SelectedChallengeMap.sigma n s))) ≤ (k : ℚ) * perElem := by
  have he : ∀ s : State, setBad read S c (SelectedChallengeMap.sigma n s) ↔
      R0P.SemSource.qm31Sample s ∈ setOf read S c := by
    intro s
    rw [setBad_iff, sigma_rho_of_ge n hn s]
  rw [mean_congr (fun s => FS.indicator_iff (he s))]
  exact qm31_set_mass_le _ k (setOf_card read S k hS c)

/-- Combining challenge: bad set of size at most 1. -/
theorem combining_mean {C X : Type} (read : C → Option X) (S : X → Finset K)
    (hS : ∀ x, (S x).card ≤ 1) (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read S c (SelectedChallengeMap.sigma n s))) ≤ capLambda := by
  have h := row_mean read S 1 hS n hn c
  simpa only [capLambda, Nat.cast_one] using h

/-- One round challenge: bad set of size at most 2. -/
theorem round_mean {C X : Type} (read : C → Option X) (S : X → Finset K)
    (hS : ∀ x, (S x).card ≤ 2) (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read S c (SelectedChallengeMap.sigma n s))) ≤ capRound := by
  have h := row_mean read S 2 hS n hn c
  simpa only [capRound, Nat.cast_ofNat] using h

/-- Batching challenge for the residual pair: bad set of size at most 21. -/
theorem pair_mean {C X : Type} (read : C → Option X) (S : X → Finset K)
    (hS : ∀ x, (S x).card ≤ 21) (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read S c (SelectedChallengeMap.sigma n s))) ≤ capPair := by
  have h := row_mean read S 21 hS n hn c
  simpa only [capPair, Nat.cast_ofNat] using h

/-! ## The model's bad sets -/

open Polynomial in
/-- Round data read from the context: the true round polynomial `g` (degree
at most 2), the running claim and the round's two certificate entries. -/
abbrev RoundData := {g : Polynomial E // g.natDegree ≤ 2} × E × E × E

/-- The model's combining bad set, `lambdaBad eK a b` with
`(a, b) = (S_W - claim, S_w - rhs2)`. -/
def lambdaSet (x : E × E) : Finset K := AspisFuture.StageD.lambdaBad eK x.1 x.2

/-- The model's round bad set, `roundBad eK g cl c0 c2`. -/
def roundSet (x : RoundData) : Finset K :=
  AspisFuture.StageD.roundBad eK x.1.1 x.2.1 x.2.2.1 x.2.2.2

/-- The model's pair bad set, `bad2 eK r0 r1` (first-fold and second-fold
residual vectors). -/
def pairSet (x : (Fin 22 → E) × (Fin 22 → E)) : Finset K :=
  AspisFuture.StageD.bad2 eK x.1 x.2

theorem lambdaSet_card (x : E × E) : (lambdaSet x).card ≤ 1 :=
  AspisFuture.StageD.lambdaBad_card_le_one eK x.1 x.2

theorem roundSet_card (x : RoundData) : (roundSet x).card ≤ 2 :=
  AspisFuture.StageD.roundBad_card_le_two eK x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2

theorem pairSet_card (x : (Fin 22 → E) × (Fin 22 → E)) : (pairSet x).card ≤ 21 :=
  AspisFuture.StageD.bad2_card_le_21 eK x.1 x.2

theorem combining_mean_model {C : Type} (read : C → Option (E × E))
    (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read lambdaSet c (SelectedChallengeMap.sigma n s))) ≤ capLambda :=
  combining_mean read lambdaSet lambdaSet_card n hn c

theorem round_mean_model {C : Type} (read : C → Option RoundData)
    (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read roundSet c (SelectedChallengeMap.sigma n s))) ≤ capRound :=
  round_mean read roundSet roundSet_card n hn c

theorem pair_mean_model {C : Type} (read : C → Option ((Fin 22 → E) × (Fin 22 → E)))
    (n : Nat) (hn : 32 ≤ n) (c : C) :
    mean (fun s : State => indicator
      (setBad read pairSet c (SelectedChallengeMap.sigma n s))) ≤ capPair :=
  pair_mean read pairSet pairSet_card n hn c

#print axioms capPair_eq_rhoCap
#print axioms perElem_eq
#print axioms capLambda_eq
#print axioms capRound_eq
#print axioms capPair_eq
#print axioms perElem_le_slack
#print axioms two_neg_124_lt_perElem
#print axioms capLambda_lt
#print axioms capRound_lt
#print axioms capPair_lt
#print axioms capLambda_le_rhoCap
#print axioms capRound_le_rhoCap
#print axioms capPair_le_rhoCap
#print axioms qm31_set_mass
#print axioms qm31_set_mass_le
#print axioms modulo_bad_mass_recovered
#print axioms sigma_rho_of_ge
#print axioms row_mean
#print axioms combining_mean
#print axioms round_mean
#print axioms pair_mean
#print axioms combining_mean_model
#print axioms round_mean_model
#print axioms pair_mean_model

end AspisRowDensity.QM31
end
