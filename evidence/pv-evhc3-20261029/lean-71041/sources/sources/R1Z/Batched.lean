import R0Z.PayloadSplit
import R1Z.BatchedAlgebra

/-! R1-2 (DESIGN-R1-PRIVACY-MODEL §2.3, §4; LOG D30, D32, D33): the R1 batched
opening block as an instance of `HonestView.BatchedLayer`.

R1 batches the 29 transported coefficient words with powers of γ (no chord
quotient), pairs the batch with the κ-batched weights of seven functionals
(inactive rows, three claim points, Libra, two OOD points), and folds twice
(α₀ on the 1024-coefficient vector, α₁ on the 256-coefficient one).  The
disclosed cells are the two round polynomials (7 coefficients each), the
query-gated folded word (`FoldedOpen`) and the 64 final coefficients.

All sums over rows are symbolic; the π reindexing is `Equiv.sum_comp`. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.Batched

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView
open AspisPool.AlgorithmicCircleDecoderV7

attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

/-! ## The cell type -/

/-- R1's batched cells: two round polynomials, the folded word, the final
coefficients. -/
inductive R1Bat
  | round0 (i : Fin 7)
  | round1 (i : Fin 7)
  | folded (p : Fin 262144)
  | final (e : Fin 64)
  deriving DecidableEq

/-- `R1Bat` as a sum of finite types (used only for `Fintype`). -/
def R1Bat.equivSum : R1Bat ≃ (Fin 7 ⊕ Fin 7) ⊕ (Fin 262144 ⊕ Fin 64) where
  toFun
    | .round0 i => .inl (.inl i)
    | .round1 i => .inl (.inr i)
    | .folded p => .inr (.inl p)
    | .final e => .inr (.inr e)
  invFun
    | .inl (.inl i) => .round0 i
    | .inl (.inr i) => .round1 i
    | .inr (.inl p) => .folded p
    | .inr (.inr e) => .final e
  left_inv b := by cases b <;> rfl
  right_inv x := by rcases x with (i | i) | (p | e) <;> rfl

instance : Fintype R1Bat := Fintype.ofEquiv _ R1Bat.equivSum.symm

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-! ## Challenge names (transcript rows 27–30) -/

abbrev gamma (ch : Challenges K) : K := ch.opening 0
abbrev kappa (ch : Challenges K) : K := ch.opening 1
abbrev alpha0 (ch : Challenges K) : K := ch.opening 2
abbrev alpha1 (ch : Challenges K) : K := ch.opening 3

/-! ## Batch and weights -/

/-- γ-batch of the 29 transported coefficient words (no quotient). -/
def batchR1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) :
    Trace K →ₗ[K] InitialMessage K :=
  ∑ c : Fin 29, ch.opening 0 ^ c.val • (coeffsLinear π).comp (LinearMap.proj c)

/-- Any functional of the batch is the γ-batch of the functional of each word. -/
theorem map_batchR1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (f : InitialMessage K →ₗ[K] K) (t : Trace K) :
    f (batchR1 π ch t) = ∑ c : Fin 29, ch.opening 0 ^ c.val * f (coeffsLinear π (t c)) := by
  simp only [batchR1, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, map_smul, smul_eq_mul]

theorem dotLinear_apply {n : Nat} (w x : Fin n → K) :
    dotLinear w x = ∑ i : Fin n, w i * x i := by
  simp only [dotLinear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]

/-- Row weights read through π: `Equiv.sum_comp`, no enumeration of rows. -/
theorem dot_reindex (π : Fin 1024 ≃ Fin 1024) (w x : InitialMessage K) :
    dotLinear (fun j => w (π.symm j)) (coeffsLinear π x) = dotLinear w x := by
  simp only [dotLinear_apply, coeffsLinear_apply]
  exact Equiv.sum_comp π.symm (fun r => w r * x r)

/- From here on `dotLinear` (a sum over 1024 rows) is never unfolded by
definitional checks. -/
attribute [local irreducible] dotLinear

/-- The seven coefficient functionals (weights.rs kinds: inactive rows, the
three claim points, Libra, the two OOD points). -/
def ell (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Fin 7 → (InitialMessage K →ₗ[K] K) :=
  ![dotLinear (fun j => AspisR0.Opening.indicator copyInactiveRows (π.symm j)),
    dotLinear (fun j => AspisR0.Opening.eqWeight (openingPoints (alpha ch) 0) (π.symm j)),
    dotLinear (fun j => AspisR0.Opening.eqWeight (openingPoints (alpha ch) 1) (π.symm j)),
    dotLinear (fun j => AspisR0.Opening.eqWeight (openingPoints (alpha ch) 2) (π.symm j)),
    dotLinear (libraWeight (alpha ch)),
    oodLinear (ch.circle 0),
    oodLinear (ch.circle 1)]

theorem ell_zero (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 0 =
    dotLinear (fun j => AspisR0.Opening.indicator copyInactiveRows (π.symm j)) := rfl
theorem ell_one (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 1 =
    dotLinear (fun j => AspisR0.Opening.eqWeight (openingPoints (alpha ch) 0) (π.symm j)) := rfl
theorem ell_two (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 2 =
    dotLinear (fun j => AspisR0.Opening.eqWeight (openingPoints (alpha ch) 1) (π.symm j)) := rfl
theorem ell_three (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 3 =
    dotLinear (fun j => AspisR0.Opening.eqWeight (openingPoints (alpha ch) 2) (π.symm j)) := rfl
theorem ell_four (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 4 =
    dotLinear (libraWeight (alpha ch)) := rfl
theorem ell_five (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 5 =
    oodLinear (ch.circle 0) := rfl
theorem ell_six (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : ell π ch 6 =
    oodLinear (ch.circle 1) := rfl

/-! ### `ell_batchR1`: each functional of the batch is the γ-batched own value -/

theorem ell_batch_inactive (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 0 (batchR1 π ch t) = ∑ c : Fin 29, ch.opening 0 ^ c.val *
      dotLinear (AspisR0.Opening.indicator copyInactiveRows) (t c) := by
  rw [ell_zero, map_batchR1]
  simp only [dot_reindex]

private theorem eq_batch (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (p : Fin 10 → K)
    (t : Trace K) :
    dotLinear (fun j => AspisR0.Opening.eqWeight p (π.symm j)) (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * dotLinear (AspisR0.Opening.eqWeight p) (t c) := by
  rw [map_batchR1]
  simp only [dot_reindex]

theorem ell_batch_claim0 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 1 (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * claimsLinear (alpha ch) 0 c t := by
  rw [ell_one, eq_batch]
  rfl

theorem ell_batch_claim1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 2 (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * claimsLinear (alpha ch) 1 c t := by
  rw [ell_two, eq_batch]
  rfl

theorem ell_batch_claim2 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 3 (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * claimsLinear (alpha ch) 2 c t := by
  rw [ell_three, eq_batch]
  rfl

theorem ell_batch_extra (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 4 (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * extraLinear π (alpha ch) c t := by
  rw [ell_four, map_batchR1]
  rfl

theorem ell_batch_ood0 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 5 (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * oodLinear (ch.circle 0) (coeffsLinear π (t c)) := by
  rw [ell_five, map_batchR1]

theorem ell_batch_ood1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) :
    ell π ch 6 (batchR1 π ch t) =
      ∑ c : Fin 29, ch.opening 0 ^ c.val * oodLinear (ch.circle 1) (coeffsLinear π (t c)) := by
  rw [ell_six, map_batchR1]

/-- κ-batched weights `w j = Σ_k κ^k ℓ_k(e_j)`. -/
def weightsR1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : InitialMessage K :=
  R1Z.BatchedAlgebra.weightsOf (ch.opening 1) (ell π ch)

theorem dot_weightsR1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (q : InitialMessage K) :
    AspisR1.RoundPairing.dot q (weightsR1 π ch) =
      ∑ k : Fin 7, ch.opening 1 ^ k.val * ell π ch k q :=
  R1Z.BatchedAlgebra.dot_weightsOf (ch.opening 1) (ell π ch) q

/-! ## The two fold layers -/

/-- The α₀-folded 256 coefficients. -/
def q1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Trace K →ₗ[K] (Fin 256 → K) :=
  (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 (ch.opening 2)).comp
    (batchR1 π ch)

def w1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Fin 256 → K :=
  AspisR1.RoundPairing.dualFold (n := 256) (ch.opening 2) (weightsR1 π ch)

def w2 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Fin 64 → K :=
  AspisR1.RoundPairing.dualFold (n := 64) (ch.opening 3) (w1 π ch)

/-- A folded symbol is disclosed iff its parent fibre holds a query. -/
def FoldedOpen (ch : Challenges K) (p : Fin 262144) : Prop :=
  ∃ u ∈ ch.queries, u.val / 4 = p.val / 4

/-- The round polynomial as a K-linear map of the message, for fixed weights. -/
def roundPolynomialLinear {n : Nat} (w : Fin (4 * n) → K) :
    (Fin (4 * n) → K) →ₗ[K] Polynomial K :=
  ∑ d : Fin n, ∑ s : Fin 4, ∑ u : Fin 4,
    (LinearMap.proj (AspisR1.childIndex d s)).smulRight
      (Polynomial.monomial (s.val + (4 - u.val) % 4)
        (AspisR1.RoundPairing.quarter * w (AspisR1.childIndex d u)))

theorem roundPolynomialLinear_apply {n : Nat} (w q : Fin (4 * n) → K) :
    roundPolynomialLinear w q = AspisR1.RoundPairing.roundPolynomial q w := by
  simp only [roundPolynomialLinear, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Polynomial.smul_monomial, smul_eq_mul,
    AspisR1.RoundPairing.roundPolynomial]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

/-! ## The read and the instance -/

/-- The R1 read of the batched block (prover.rs prove_from_semantics). -/
def r1Read (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Trace K →ₗ[K] (R1Bat → K) :=
  LinearMap.pi fun b => match b with
  | .round0 i => (Polynomial.lcoeff K i.val).comp
      ((roundPolynomialLinear (n := 256) (weightsR1 π ch)).comp (batchR1 π ch))
  | .round1 i => (Polynomial.lcoeff K i.val).comp
      ((roundPolynomialLinear (n := 64) (w1 π ch)).comp (q1 π ch))
  | .folded p => if FoldedOpen ch p then
      (LinearMap.proj p).comp (AspisWide.FinalEncoder.exactFinalLinear.comp (q1 π ch)) else 0
  | .final e => (LinearMap.proj e).comp
      ((AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 (ch.opening 3)).comp
        (q1 π ch))

instance instBatchedLayer : BatchedLayer K R1Bat where
  read := r1Read

/-- R1 payload cells. -/
abbrev R1Payload (K : Type) := Payload K R1Bat

attribute [local irreducible] batchR1 weightsR1 w1 q1 roundPolynomialLinear

/-! ## `batRead_L`: the four cell formulas -/

theorem read_round0 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (i : Fin 7) :
    BatchedLayer.read (Bat := R1Bat) π ch t (.round0 i) =
      (AspisR1.RoundPairing.roundPolynomial (n := 256) (batchR1 π ch t) (weightsR1 π ch)).coeff
        i.val := by
  show r1Read π ch t (.round0 i) = _
  simp only [r1Read, LinearMap.pi_apply, LinearMap.comp_apply, Polynomial.lcoeff_apply,
    roundPolynomialLinear_apply]

theorem read_round1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (i : Fin 7) :
    BatchedLayer.read (Bat := R1Bat) π ch t (.round1 i) =
      (AspisR1.RoundPairing.roundPolynomial (n := 64) (q1 π ch t) (w1 π ch)).coeff i.val := by
  show r1Read π ch t (.round1 i) = _
  simp only [r1Read, LinearMap.pi_apply, LinearMap.comp_apply, Polynomial.lcoeff_apply,
    roundPolynomialLinear_apply]

theorem read_folded (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K)
    (p : Fin 262144) (h : FoldedOpen ch p) :
    BatchedLayer.read (Bat := R1Bat) π ch t (.folded p) =
      AspisWide.FinalEncoder.exactFinalLinear (q1 π ch t) p := by
  show r1Read π ch t (.folded p) = _
  simp only [r1Read, LinearMap.pi_apply, if_pos h, LinearMap.comp_apply, LinearMap.proj_apply]

theorem folded_unqueried_zero (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K)
    (p : Fin 262144) (h : ¬ FoldedOpen ch p) :
    BatchedLayer.read (Bat := R1Bat) π ch t (.folded p) = 0 := by
  show r1Read π ch t (.folded p) = _
  simp only [r1Read, LinearMap.pi_apply, if_neg h, LinearMap.zero_apply]

theorem read_final (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (e : Fin 64) :
    BatchedLayer.read (Bat := R1Bat) π ch t (.final e) =
      AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 (ch.opening 3)
        (q1 π ch t) e := rfl

/-- The payload's batched cells are the R1 read (no other cell is touched). -/
theorem L_bat {F : Subfield K} (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) (b : R1Bat) :
    R0Z.PayloadSplit.L (Bat := R1Bat) π B ch t (.bat b) =
      BatchedLayer.read (Bat := R1Bat) π ch t b := rfl

#print axioms R1Bat.equivSum
#print axioms map_batchR1
#print axioms dot_reindex
#print axioms ell_batch_inactive
#print axioms ell_batch_claim0
#print axioms ell_batch_claim1
#print axioms ell_batch_claim2
#print axioms ell_batch_extra
#print axioms ell_batch_ood0
#print axioms ell_batch_ood1
#print axioms dot_weightsR1
#print axioms roundPolynomialLinear_apply
#print axioms read_round0
#print axioms read_round1
#print axioms read_folded
#print axioms folded_unqueried_zero
#print axioms read_final
#print axioms L_bat

end R1Z.Batched

end
