import R0Z.ViewAffine

/-! Disclosed field payload for the 32-round ideal masked reference.
Only queried symbols are nonzero in the opened-symbol vector. Its public
zero extension gives a fixed vector space without disclosing other symbols.
Polynomials use coefficient arrays, of lengths 28 (semantic) and 7 (opening).
All finite sums and encoders remain symbolic; no concrete universe is run.
Source citations and the ideal/source boundary are recorded in ../../LOG.md. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.HonestView
open R0P R0P.SemSource R0Z.MaskLayout R0Z.ViewAffine Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisWide.InitialEncoder
open AspisWide.Agreement AspisR0.Opening AspisR0.Chord AspisR0.ChordGeometry
open AspisV5ComponentCConcreteFoldLinearity
open AspisR0.PolynomialPair AspisR0.RoundNormalization AspisR0.Fold
attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Grouped challenge values: 25 semantic, two circle, four opening scalars,
then the q22 set. Empty/other sets are retained; no good-challenge restriction. -/
structure Challenges (K : Type) [Field K] where
  sem : Fin 25 → K
  circle : Fin 2 → Point K
  opening : Fin 4 → K
  queries : Finset (Fin 262144)

def alpha (ch : Challenges K) : Fin 10 → K := fun i => ch.sem ⟨15+i.val, by omega⟩
def zc (ch : Challenges K) : Fin 10 → K := fun i => ch.sem ⟨3+i.val, by omega⟩

/-- D9. Literal weighted reciprocals, logup.rs:192–224. Zero weights
contribute zero, including at a zero denominator. The source ActivePole
branch is ZR1; it has no model element and induces no conditioning here. -/
def helper (pub : Public K) (t : Trace K) (lam chi : K) (r : Fin 1024) : K :=
  let row := copyRowsAt pub lam t r
  (∑ s : Fin 2, (chi-row.producerValues s)⁻¹ * row.producerWeights s) -
    ∑ s : Fin 2, (chi-row.consumerValues s)⁻¹ * row.consumerWeights s

/-- H1 is constructed after lambda/chi and before applying its affine padding. -/
def prepare (pub : Public K) (t : Trace K) (ch : Challenges K) : Trace K :=
  fun c r => if c.val = 26 then helper pub t (ch.sem 0) (ch.sem 1) r else t c r

inductive PayloadCell
  | maskSum
  | semanticCoeff (round : Fin 10) (coefficient : Fin 28)
  | pointClaim (point : Fin 3) (column : Fin 29)
  | ood (point : Fin 2) (column : Fin 29)
  | inactiveSum
  | openingCoeff (coefficient : Fin 7)
  | finalCoeff (coefficient : Fin 256)
  | opened (query : Fin 262144) (child : Fin 4) (column : Fin 29)
  deriving DecidableEq, Fintype

abbrev Payload (K : Type) := PayloadCell → K

/-- Linear evaluation of a coordinate vector against fixed weights. -/
def dotLinear {n : Nat} (weights : Fin n → K) : (Fin n → K) →ₗ[K] K :=
  ∑ i : Fin n, weights i • LinearMap.proj i

def claimsLinear (a : Fin 10 → K) (j : Fin 3) (c : Fin 29) : Trace K →ₗ[K] K :=
  (dotLinear (eqWeight (openingPoints a j))).comp (LinearMap.proj c)

theorem claimsLinear_apply (a : Fin 10 → K) (j : Fin 3) (c : Fin 29) (t : Trace K) :
    claimsLinear a j c t = honestClaims t a j c := by
  simp only [claimsLinear, dotLinear, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, honestClaims,
    AspisR0.LinearDual.dot]

/-- R0/Chord.evalMessage in the exact natural coefficient basis. -/
def oodLinear (z : Point K) : InitialMessage K →ₗ[K] K :=
  (Polynomial.leval z.1.1).comp p0Linear + z.1.2 • (Polynomial.leval z.1.1).comp p1Linear

def cell (B : PackBasis F) (t : Trace K) (a : Fin 10 → K) (j : Fin 3) (c : Fin 29) :
    AffTape K F →ᵃ[F] K :=
  ((claimsLinear a j c).restrictScalars F).toAffineMap.comp (traceAffine B t)

theorem cell_apply (B : PackBasis F) (t : Trace K) (a : Fin 10 → K)
    (j : Fin 3) (c : Fin 29) (r : AffTape K F) :
    cell B t a j c r = honestClaims (applyAff B t r) a j c := by
  simp only [cell, AffineMap.comp_apply, LinearMap.coe_toAffineMap,
    LinearMap.restrictScalars_apply, traceAffine_apply, claimsLinear_apply]

theorem semantic_claim_fixed (B : PackBasis F) (t : Trace K) (a : Fin 10 → K)
    (j : Fin 3) (c : Fin 16) (r : AffTape K F) :
    honestClaims (applyAff B t r) a j (Fin.castLE (by omega) c) =
      honestClaims t a j (Fin.castLE (by omega) c) := by
  have hc : (applyAff B t r) (Fin.castLE (by omega) c) = t (Fin.castLE (by omega) c) := by
    funext s
    simp only [applyAff, Fin.val_castLE, if_pos c.isLt]
  simp only [honestClaims, hc]

def semanticOpenings (t : Trace K) (a : Fin 10 → K) : Openings K :=
  ⟨fun c => honestClaims t a 0 (Fin.castLE (by omega) c),
    fun c => honestClaims t a 1 (Fin.castLE (by omega) c),
    fun c => honestClaims t a 2 (Fin.castLE (by omega) c)⟩

/-- The slope includes the instance-dependent copy-denominator contribution.
`originalAt_decomp` is proved from `originalAt_affine`, not a premise. -/
def original (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (a : Fin 10 → K) : AffTape K F →ᵃ[F] K :=
  let f := fun h => originalAt pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13)
    (zc ch) B (semanticOpenings t a) h a
  AffineMap.const F _ (f 0) + (f 1-f 0) • cell B t a 0 26

theorem original_apply (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (a : Fin 10 → K) (r : AffTape K F) :
    original pub B t ch a r = terminalValue pub (ch.sem 0) (ch.sem 1)
      (ch.sem 2) (ch.sem 13) (zc ch) B (honestClaims (applyAff B t r) a) a := by
  rw [terminalValue_eq_originalAt]
  have ho : (⟨fun c => honestClaims (applyAff B t r) a 0 (Fin.castLE (by omega) c),
      fun c => honestClaims (applyAff B t r) a 1 (Fin.castLE (by omega) c),
      fun c => honestClaims (applyAff B t r) a 2 (Fin.castLE (by omega) c)⟩ : Openings K) =
        semanticOpenings t a := by
    simp only [semantic_claim_fixed, semanticOpenings]
  rw [ho, originalAt_decomp]
  change _ + _ * cell B t a 0 26 r = _
  rw [cell_apply]
  simp only [AffineMap.const_apply]
  ring

def mask (B : PackBasis F) (t : Trace K) (a : Fin 10 → K) : AffTape K F →ᵃ[F] K :=
  (∑ c : Fin 16, (MaskedProtocol.maskFactors B a).c1 c •
    cell B t a 0 (Fin.castLE (by omega) c)) +
    (MaskedProtocol.maskFactors B a).explicitG • cell B t a 0 27 +
    ∑ c : Fin 10, (MaskedProtocol.maskFactors B a).maskOnly c •
      cell B t a 0 ⟨16+c.val, by omega⟩

def oracle (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (a : Fin 10 → K) : AffTape K F →ᵃ[F] K :=
  mask B t a + ch.sem 14 • original pub B t ch a

/-- Prefix/variable/Boolean-tail point for round j, big-endian coordinates. -/
def roundPoint (ch : Challenges K) (j : Fin 10) (z : K)
    (tail : Fin (9-j.val) → Bool) : Fin 10 → K := fun i =>
  if hlt : i.val < j.val then alpha ch i else if heq : i.val = j.val then z
  else if tail ⟨i.val-j.val-1, by omega⟩ then 1 else 0

/-- state_only_zerocheck.rs:95–128: interpolate the partial Boolean sums. -/
def roundPoly (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (j : Fin 10) : AffTape K F →ᵃ[F] K[X] :=
  ((Lagrange.interpolate Finset.univ (fun i : Fin 28 => (i.val : K))).restrictScalars F).toAffineMap.comp
    (AffineMap.pi fun i => ∑ tail : Fin (9-j.val) → Bool,
      oracle pub B t ch (roundPoint ch j (i.val : K) tail))

/-- Chord subtraction and pointwise division are linear at fixed circle points.
The exact encoder's linear left inverse decodes its image uniquely. Its
extension off the image is total, as are the field divisions. -/
def quotientLinear (z0 z1 : Point K) : InitialMessage K →ₗ[K] InitialMessage K :=
  let values := LinearMap.pi fun i : Fin 2 => oodLinear (if i = 0 then z0 else z1)
  let interp := (interpolationLinear z0 z1).comp values
  let numerator := exactInitialLinear.comp (LinearMap.id - interp)
  let word := LinearMap.pi fun i => (L z0 z1 i)⁻¹ • ((LinearMap.proj i).comp numerator)
  exactInitialLinear.leftInverse.comp word

def batchLinear (ch : Challenges K) : Trace K →ₗ[K] InitialMessage K :=
  ∑ c : Fin 29, ch.opening 0 ^ c.val •
    (quotientLinear (ch.circle 0) (ch.circle 1)).comp (LinearMap.proj c)

/-- OpeningDefinitions.totalWeights never reads the zeroed word/claim fields. -/
def openingWeights (ch : Challenges K) : InitialMessage K :=
  totalWeights ⟨0, ch.circle 0, ch.circle 1, 0, openingPoints (alpha ch), 0, copyInactiveRows⟩
    (ch.opening 1) (ch.opening 2)

def relationLinear (w : InitialMessage K) : InitialMessage K →ₗ[K] K[X] :=
  ∑ d : Fin 256, ∑ s : Fin 4, ∑ u : Fin 4,
    (LinearMap.proj (childIndex d s)).smulRight
      (monomial (s.val + (4-u.val)%4) (quarter * w (childIndex d u)))

def foldLinear (a : K) : InitialMessage K →ₗ[K] (Fin 256 → K) :=
  LinearMap.pi fun d => ∑ s : Fin 4, a^s.val • LinearMap.proj (childIndex d s)

def linearPayload (ch : Challenges K) : Trace K →ₗ[K] Payload K :=
  LinearMap.pi fun coord => match coord with
  | .maskSum | .semanticCoeff _ _ => 0
  | .pointClaim j c => claimsLinear (alpha ch) j c
  | .ood j c => (oodLinear (ch.circle j)).comp (LinearMap.proj c)
  | .inactiveSum => ∑ c : Fin 29, ch.opening 0 ^ c.val •
      (dotLinear (indicator copyInactiveRows)).comp (LinearMap.proj c)
  | .openingCoeff i => (Polynomial.lcoeff K i.val).comp
      ((relationLinear (openingWeights ch)).comp (batchLinear ch))
  | .finalCoeff i => (LinearMap.proj i).comp ((foldLinear (ch.opening 3)).comp (batchLinear ch))
  | .opened q s c => if q ∈ ch.queries then
      (LinearMap.proj (childIndex q s)).comp (exactInitialLinear.comp (LinearMap.proj c)) else 0

def payloadAffine (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) : AffTape K F →ᵃ[F] Payload K :=
  let t := prepare pub t ch
  AffineMap.pi fun coord => match coord with
  | .maskSum => ∑ bits : Fin 10 → Bool, mask B t (fun i => if bits i then 1 else 0)
  | .semanticCoeff j i => ((Polynomial.lcoeff K i.val).restrictScalars F).toAffineMap.comp
      (roundPoly pub B t ch j)
  | coord => (((LinearMap.proj coord).comp (linearPayload ch)).restrictScalars F).toAffineMap.comp
      (traceAffine B t)

/-- Evaluation of an affine-map sum, proved on an abstract finite index set. -/
theorem affine_sum_apply {T V I : Type} [AddCommGroup T] [Module F T]
    [AddCommGroup V] [Module F V] (s : Finset I) (f : I → T →ᵃ[F] V) (r : T) :
    (∑ i ∈ s, f i) r = ∑ i ∈ s, f i r := by
  let ev : (T →ᵃ[F] V) →+ V :=
    { toFun := fun f => f r, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev f s

theorem mask_apply (B : PackBasis F) (t : Trace K) (a : Fin 10 → K) (r : AffTape K F) :
    mask B t a r = MaskedProtocol.maskValue B
      (fun c => honestClaims (applyAff B t r) a 0 (Fin.castLE (by omega) c))
      (fun c => honestClaims (applyAff B t r) a 0 ⟨16+c.val, by omega⟩)
      (honestClaims (applyAff B t r) a 0 27) a := by
  simp only [mask, AffineMap.coe_add, Pi.add_apply, affine_sum_apply,
    AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, cell_apply, MaskedProtocol.maskValue]

theorem oracle_apply (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (a : Fin 10 → K) (r : AffTape K F) :
    oracle pub B t ch a r = MaskedProtocol.terminalZ pub
      (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (ch.sem 14) (zc ch) B
      (honestClaims (applyAff B t r) a) a := by
  simp only [oracle, AffineMap.coe_add, Pi.add_apply, AffineMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, mask_apply, original_apply, MaskedProtocol.terminalZ]

theorem oodLinear_apply (z : Point K) (q : InitialMessage K) :
    oodLinear z q = evalMessage q z := by
  simp only [oodLinear, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    smul_eq_mul, p0Linear_apply, p1Linear_apply, Polynomial.leval_apply, evalMessage]

theorem relationLinear_apply (w q : InitialMessage K) :
    relationLinear w q = roundPolynomial q w := by
  simp only [relationLinear, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Polynomial.smul_monomial, smul_eq_mul, roundPolynomial]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem foldLinear_apply (a : K) (q : InitialMessage K) :
    foldLinear a q = foldMessage a q := by
  funext d
  simp only [foldLinear, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, foldMessage_eq_sum, mul_comm]

/-- The decoder used above is exactly an inverse on the encoded image. -/
theorem decode_encoded (q : InitialMessage K) :
    (exactInitialLinear (E := K)).leftInverse (exactInitialEncoder q) = q := by
  exact LinearMap.leftInverse_apply_of_inj (f := exactInitialLinear (E := K))
    (LinearMap.ker_eq_bot.mpr exactInitialEncoder_injective) q

/-- The ten round messages are interpolation of the actual masked terminal's
partial Boolean sums. This also shows that H1 affinity passes through the
round-polynomial construction, with earlier alphas fixed. -/
theorem roundPoly_apply (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (j : Fin 10) (r : AffTape K F) :
    roundPoly pub B t ch j r =
      Lagrange.interpolate Finset.univ (fun i : Fin 28 => (i.val : K))
        (fun i => ∑ tail : Fin (9-j.val) → Bool,
          let a := roundPoint ch j (i.val : K) tail
          MaskedProtocol.terminalZ pub (ch.sem 0) (ch.sem 1) (ch.sem 2)
            (ch.sem 13) (ch.sem 14) (zc ch) B (honestClaims (applyAff B t r) a) a) := by
  simp only [roundPoly, AffineMap.comp_apply, LinearMap.coe_toAffineMap,
    LinearMap.restrictScalars_apply]
  congr 1
  funext i
  simp only [AffineMap.pi_apply, affine_sum_apply, oracle_apply]

/-- The public zero extension reveals no symbol at an unqueried position. -/
theorem unqueried_zero (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (q : Fin 262144) (s : Fin 4) (c : Fin 29)
    (hq : q ∉ ch.queries) : payloadAffine pub B t ch r (.opened q s c) = 0 := by
  simp only [payloadAffine, AffineMap.pi_apply, AffineMap.comp_apply,
    LinearMap.coe_toAffineMap, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, LinearMap.pi_apply, if_neg hq, LinearMap.zero_apply]

/-- Direct honest payload: first apply the ported mask to the prepared trace,
then evaluate the semantic/oracle/opening expressions. The affine packaging is
proved equal to this function below, not required as an interface premise. -/
def run (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) : Payload K :=
  let t := applyAff B (prepare pub t ch) r
  fun coord => match coord with
  | .maskSum => ∑ bits : Fin 10 → Bool,
      let a := fun i => if bits i then (1 : K) else 0
      MaskedProtocol.maskValue B
        (fun c => honestClaims t a 0 (Fin.castLE (by omega) c))
        (fun c => honestClaims t a 0 ⟨16+c.val, by omega⟩) (honestClaims t a 0 27) a
  | .semanticCoeff j i =>
      (Lagrange.interpolate Finset.univ (fun k : Fin 28 => (k.val : K))
        (fun k => ∑ tail : Fin (9-j.val) → Bool,
          let a := roundPoint ch j (k.val : K) tail
          MaskedProtocol.terminalZ pub (ch.sem 0) (ch.sem 1) (ch.sem 2)
            (ch.sem 13) (ch.sem 14) (zc ch) B (honestClaims t a) a)).coeff i.val
  | .pointClaim j c => honestClaims t (alpha ch) j c
  | .ood j c => evalMessage (t c) (ch.circle j)
  | .inactiveSum => ∑ c : Fin 29, ch.opening 0 ^ c.val *
      AspisR0.LinearDual.dot (indicator copyInactiveRows) (t c)
  | .openingCoeff i => (roundPolynomial (batchLinear ch t) (openingWeights ch)).coeff i.val
  | .finalCoeff i => foldMessage (ch.opening 3) (batchLinear ch t) i
  | .opened q s c => if q ∈ ch.queries then exactInitialEncoder (t c) (childIndex q s) else 0

attribute [local irreducible] prepare helper applyAff traceAffine batchLinear
  quotientLinear openingWeights honestClaims MaskedProtocol.terminalZ MaskedProtocol.maskValue
  mask claimsLinear dotLinear relationLinear

private theorem run_maskSum (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) :
    run pub B t ch r (.maskSum) = payloadAffine pub B t ch r (.maskSum) := by
  simp only [payloadAffine, AffineMap.pi_apply]
  rw [affine_sum_apply]
  simp only [run, mask_apply]

private theorem run_semanticCoeff (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (j : Fin 10) (i : Fin 28) :
    run pub B t ch r (.semanticCoeff j i) = payloadAffine pub B t ch r (.semanticCoeff j i) := by
  change _ = (roundPoly pub B (prepare pub t ch) ch j r).coeff i.val
  exact (congrArg (fun p : K[X] => p.coeff i.val)
    (roundPoly_apply pub B (prepare pub t ch) ch j r)).symm

private theorem run_pointClaim (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (j : Fin 3) (c : Fin 29) :
    run pub B t ch r (.pointClaim j c) = payloadAffine pub B t ch r (.pointClaim j c) := by
  simp only [payloadAffine, AffineMap.pi_apply, AffineMap.comp_apply,
    LinearMap.coe_toAffineMap, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, LinearMap.pi_apply]
  change _ = claimsLinear (alpha ch) j c (traceAffine B (prepare pub t ch) r)
  rw [traceAffine_apply, claimsLinear_apply]
  rfl

private theorem run_ood (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (j : Fin 2) (c : Fin 29) :
    run pub B t ch r (.ood j c) = payloadAffine pub B t ch r (.ood j c) := by
  change _ = oodLinear (ch.circle j) ((traceAffine B (prepare pub t ch) r) c)
  rw [traceAffine_apply, oodLinear_apply]
  rfl

private theorem run_inactiveSum (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) :
    run pub B t ch r (.inactiveSum) = payloadAffine pub B t ch r (.inactiveSum) := by
  simp only [payloadAffine, AffineMap.pi_apply, AffineMap.comp_apply,
    LinearMap.coe_toAffineMap, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, LinearMap.pi_apply]
  change _ = (∑ c : Fin 29, ch.opening 0 ^ c.val •
    (dotLinear (indicator copyInactiveRows)).comp (LinearMap.proj c))
    (traceAffine B (prepare pub t ch) r)
  rw [traceAffine_apply]
  simp only [run, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, smul_eq_mul, dotLinear, AspisR0.LinearDual.dot]

private theorem run_openingCoeff (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (i : Fin 7) :
    run pub B t ch r (.openingCoeff i) = payloadAffine pub B t ch r (.openingCoeff i) := by
  simp only [payloadAffine, AffineMap.pi_apply, AffineMap.comp_apply,
    LinearMap.coe_toAffineMap, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, LinearMap.pi_apply, Polynomial.lcoeff_apply]
  change _ = (relationLinear (openingWeights ch)
    (batchLinear ch (traceAffine B (prepare pub t ch) r))).coeff i.val
  rw [traceAffine_apply, relationLinear_apply]
  rfl

private theorem run_finalCoeff (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (i : Fin 256) :
    run pub B t ch r (.finalCoeff i) = payloadAffine pub B t ch r (.finalCoeff i) := by
  change _ = foldLinear (ch.opening 3)
    (batchLinear ch (traceAffine B (prepare pub t ch) r)) i
  rw [traceAffine_apply, foldLinear_apply]
  rfl

private theorem run_opened (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (q : Fin 262144) (s : Fin 4) (c : Fin 29) :
    run pub B t ch r (.opened q s c) = payloadAffine pub B t ch r (.opened q s c) := by
  change _ = (if q ∈ ch.queries then
    (LinearMap.proj (childIndex q s)).comp (exactInitialLinear.comp (LinearMap.proj c))
    else 0) (traceAffine B (prepare pub t ch) r)
  rw [traceAffine_apply]
  simp only [run]
  split_ifs <;> simp only [LinearMap.comp_apply, LinearMap.proj_apply,
    exactInitialLinear_apply, LinearMap.zero_apply]

/-- Componentwise equality to the actual ported expressions. The eight small
component lemmas keep the kernel from expanding one aggregate proof. -/
theorem run_eq_payloadAffine (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) : run pub B t ch r = payloadAffine pub B t ch r := by
  funext coord
  cases coord with
  | maskSum => exact run_maskSum pub B t ch r
  | semanticCoeff j i => exact run_semanticCoeff pub B t ch r j i
  | pointClaim j c => exact run_pointClaim pub B t ch r j c
  | ood j c => exact run_ood pub B t ch r j c
  | inactiveSum => exact run_inactiveSum pub B t ch r
  | openingCoeff i => exact run_openingCoeff pub B t ch r i
  | finalCoeff i => exact run_finalCoeff pub B t ch r i
  | opened q s c => exact run_opened pub B t ch r q s c

#print axioms helper
#print axioms original_apply
#print axioms semantic_claim_fixed
#print axioms payloadAffine
#print axioms mask_apply
#print axioms oracle_apply
#print axioms oodLinear_apply
#print axioms relationLinear_apply
#print axioms foldLinear_apply
#print axioms decode_encoded
#print axioms roundPoly_apply
#print axioms unqueried_zero
#print axioms run_eq_payloadAffine
end R0Z.HonestView
