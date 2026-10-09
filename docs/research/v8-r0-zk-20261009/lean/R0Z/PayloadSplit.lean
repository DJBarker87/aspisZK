import R0Z.Partition

/-! The disclosed payload is a linear observation of the prepared trace plus
only the original terminal's round-polynomial contribution. All encoders,
interpolations, query gates and finite sums stay symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.PayloadSplit
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition Polynomial
attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

abbrev PointFunction (K : Type) := (Fin 10 → K) → K

def maskLinear (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (a : Fin 10 → K) : Trace K →ₗ[K] K :=
  (∑ c : Fin 16, (MaskedProtocol.maskFactors B a).c1 c •
    claimsLinear a 0 (Fin.castLE (by omega) c)) +
    (MaskedProtocol.maskFactors B a).explicitG • claimsLinear a 0 27 +
    (∑ c : Fin 10, (MaskedProtocol.maskFactors B a).maskOnly c •
      claimsLinear a 0 ⟨16+c.val, by omega⟩) + extraLinear π a 28

theorem maskLinear_apply (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (a : Fin 10 → K) (t : Trace K) :
    maskLinear π B a t = MaskedProtocol.maskValue B
      (fun c => honestClaims t a 0 (Fin.castLE (by omega) c))
      (fun c => honestClaims t a 0 ⟨16+c.val, by omega⟩) (honestClaims t a 0 27) a + R0P.Mask.honestExtra π t a 28 := by
  simp only [maskLinear, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, claimsLinear_apply, extraLinear_apply, MaskedProtocol.maskValue]

def rounds (ch : Challenges K) (j : Fin 10) : PointFunction K →ₗ[K] K[X] :=
  (Lagrange.interpolate Finset.univ (fun k : Fin 28 => (k.val : K))).comp
    (LinearMap.pi fun k => ∑ tail : Fin (9-j.val) → Bool,
      LinearMap.proj (roundPoint ch j (k.val : K) tail))

theorem rounds_apply (ch : Challenges K) (j : Fin 10) (f : PointFunction K) :
    rounds ch j f = Lagrange.interpolate Finset.univ (fun k : Fin 28 => (k.val : K))
      (fun k => ∑ tail : Fin (9-j.val) → Bool, f (roundPoint ch j (k.val : K) tail)) := by
  unfold rounds
  rw [LinearMap.comp_apply]
  congr 1
  funext k
  simp only [LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply]

/-- All mask contributions, including the round masks, and all direct linear
observations. This map does not read the instance or either tape. -/
def L (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : Trace K →ₗ[K] Payload K :=
  LinearMap.pi fun coord => match coord with
  | .maskSum => ∑ bits : Fin 10 → Bool, maskLinear π B (fun i => if bits i then 1 else 0)
  | .semanticCoeff j i => (Polynomial.lcoeff K i.val).comp
      ((rounds ch j).comp (LinearMap.pi (maskLinear π B)))
  | coord => (LinearMap.proj coord).comp (linearPayload π ch)

abbrev RoundPayload (K : Type) := Fin 10 → Fin 28 → K

def roundInclusion : RoundPayload K →ₗ[K] Payload K :=
  LinearMap.pi fun coord => match coord with
  | .semanticCoeff j i => (LinearMap.proj i : (Fin 28 → K) →ₗ[K] K).comp
      (LinearMap.proj j : RoundPayload K →ₗ[K] (Fin 28 → K))
  | _ => 0

def originalRounds (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) : RoundPayload K := fun j i =>
  (rounds ch j (fun a => ch.sem 14 * terminalValue pub (ch.sem 0) (ch.sem 1)
    (ch.sem 2) (ch.sem 13) (zc ch) B (honestClaims t a) a)).coeff i.val

def O (pub : Public K) (B : PackBasis F) (ch : Challenges K) (t : Trace K) : Payload K :=
  roundInclusion (originalRounds pub B ch t)

def actual (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (r : T K F) : Trace K :=
  applyAff B (prepare pub (applyEligible t r.2.2) ch) (aff r)

def payload (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (r : T K F) : Payload K :=
  run π pub B (applyEligible t r.2.2) ch (aff r)

theorem L_round (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (t : Trace K)
    (j : Fin 10) (i : Fin 28) :
    L π B ch t (.semanticCoeff j i) = (rounds ch j (fun a => maskLinear π B a t)).coeff i.val := rfl

theorem O_round (pub : Public K) (B : PackBasis F) (ch : Challenges K) (t : Trace K)
    (j : Fin 10) (i : Fin 28) :
    O pub B ch t (.semanticCoeff j i) = originalRounds pub B ch t j i := rfl

attribute [local irreducible] prepare helper applyAff traceAffine batchLinear
  quotientLinear openingWeights honestClaims MaskedProtocol.terminalZ MaskedProtocol.maskValue
  claimsLinear dotLinear relationLinear

private theorem run_split_maskSum (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) :
    run π pub B t ch r (.maskSum) = L π B ch (applyAff B (prepare pub t ch) r) (.maskSum) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.maskSum) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.sum_apply,
    maskLinear_apply, Pi.add_apply, LinearMap.zero_apply, add_zero]

private theorem run_split_semanticCoeff (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (j : Fin 10) (i : Fin 28) :
    run π pub B t ch r (.semanticCoeff j i) = L π B ch (applyAff B (prepare pub t ch) r) (.semanticCoeff j i) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.semanticCoeff j i) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [Pi.add_apply, L_round, O_round]
  change _ = (rounds ch j (fun a => maskLinear π B a u)).coeff i.val +
    (rounds ch j (fun a => ch.sem 14 * terminalValue pub (ch.sem 0) (ch.sem 1)
      (ch.sem 2) (ch.sem 13) (zc ch) B (honestClaims u a) a)).coeff i.val
  rw [← Polynomial.coeff_add, ← map_add]
  simp only [rounds_apply, Pi.add_apply, maskLinear_apply, run, MaskedProtocol.terminalZ, u]

private theorem run_split_pointClaim (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (j : Fin 3) (c : Fin 29) :
    run π pub B t ch r (.pointClaim j c) = L π B ch (applyAff B (prepare pub t ch) r) (.pointClaim j c) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.pointClaim j c) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, claimsLinear_apply, Pi.add_apply,
    LinearMap.zero_apply, add_zero]

private theorem run_split_extraClaim (π : Fin 1024 ≃ Fin 1024) (pub : Public K)
    (B : PackBasis F) (t : Trace K) (ch : Challenges K) (r : AffTape K F) (c : Fin 29) :
    run π pub B t ch r (.extraClaim c) = L π B ch (applyAff B (prepare pub t ch) r) (.extraClaim c) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.extraClaim c) := by
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, extraLinear_apply, Pi.add_apply,
    LinearMap.zero_apply, add_zero]

private theorem run_split_ood (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (j : Fin 2) (c : Fin 29) :
    run π pub B t ch r (.ood j c) = L π B ch (applyAff B (prepare pub t ch) r) (.ood j c) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.ood j c) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, coeffsLinear_apply, oodLinear_apply, Pi.add_apply,
    LinearMap.zero_apply, add_zero]
  rfl

private theorem run_split_inactiveSum (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) :
    run π pub B t ch r (.inactiveSum) = L π B ch (applyAff B (prepare pub t ch) r) (.inactiveSum) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.inactiveSum) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, LinearMap.sum_apply, LinearMap.smul_apply,
    dotLinear, smul_eq_mul, AspisR0.LinearDual.dot, Pi.add_apply,
    LinearMap.zero_apply, add_zero]

private theorem run_split_openingCoeff (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (i : Fin 7) :
    run π pub B t ch r (.openingCoeff i) = L π B ch (applyAff B (prepare pub t ch) r) (.openingCoeff i) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.openingCoeff i) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, Polynomial.lcoeff_apply, relationLinear_apply,
    Pi.add_apply, LinearMap.zero_apply, add_zero]

private theorem run_split_finalCoeff (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (i : Fin 256) :
    run π pub B t ch r (.finalCoeff i) = L π B ch (applyAff B (prepare pub t ch) r) (.finalCoeff i) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.finalCoeff i) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, foldLinear_apply, Pi.add_apply,
    LinearMap.zero_apply, add_zero]

private theorem run_split_opened (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) (q : Fin 262144) (s : Fin 4) (c : Fin 29) :
    run π pub B t ch r (.opened q s c) = L π B ch (applyAff B (prepare pub t ch) r) (.opened q s c) +
      O pub B ch (applyAff B (prepare pub t ch) r) (.opened q s c) := by
  let u := applyAff B (prepare pub t ch) r
  simp only [run, L, O, roundInclusion, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, linearPayload, Pi.add_apply, LinearMap.zero_apply, add_zero]
  split_ifs <;> simp only [LinearMap.comp_apply, LinearMap.proj_apply,
    AspisWide.Agreement.exactInitialLinear_apply, LinearMap.zero_apply, coeffsLinear_apply]
  rfl

/-- Componentwise equality to the existing honest view, without layout assumptions. -/
theorem run_split (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : AffTape K F) :
    run π pub B t ch r = L π B ch (applyAff B (prepare pub t ch) r) +
      O pub B ch (applyAff B (prepare pub t ch) r) := by
  funext coord
  cases coord with
  | maskSum => exact run_split_maskSum π pub B t ch r
  | semanticCoeff j i => exact run_split_semanticCoeff π pub B t ch r j i
  | pointClaim j c => exact run_split_pointClaim π pub B t ch r j c
  | extraClaim c => exact run_split_extraClaim π pub B t ch r c
  | ood j c => exact run_split_ood π pub B t ch r j c
  | inactiveSum => exact run_split_inactiveSum π pub B t ch r
  | openingCoeff i => exact run_split_openingCoeff π pub B t ch r i
  | finalCoeff i => exact run_split_finalCoeff π pub B t ch r i
  | opened q s c => exact run_split_opened π pub B t ch r q s c

theorem actual_add_pure (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (m : M K F) (n : N K F) :
    actual pub B t ch (m,n) = actual pub B t ch (0,n) + pureTrace B m := by
  have ha : aff (m,n) = aff (0,n) + pureAff m := by
    change aff (m,n) = aff (0,n) + aff (m,0)
    rw [← map_add]
    congr 1
    simp
  simp only [actual, applyAff_eq_base_add, ha, map_add, pureTrace, LinearMap.comp_apply,
    add_assoc]

theorem claim_add_pure (B : PackBasis F) (t : Trace K) (m : M K F)
    (a : Fin 10 → K) (j : Fin 3) (c : Fin 29) (hc : c.val < 16 ∨ c.val = 26) :
    honestClaims (t + pureTrace B m) a j c = honestClaims t a j c := by
  have he : (t + pureTrace B m) c = t c := by
    simp only [Pi.add_apply, pureTrace_fixed B m c hc, add_zero]
  simp only [honestClaims, he]

/-- The actual terminal never reads G, D, or any mask-only column. -/
theorem terminal_add_pure (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (m : M K F) (a : Fin 10 → K) :
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims (t + pureTrace B m) a) a =
    terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
      (honestClaims t a) a := by
  have hs (j : Fin 3) (c : Fin 16) := claim_add_pure B t m a j
    (Fin.castLE (by omega) c) (Or.inl c.isLt)
  have hh := claim_add_pure B t m a 0 26 (Or.inr rfl)
  simp only [terminalValue, hs, hh]

theorem O_add_pure (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (m : M K F) :
    O pub B ch (t + pureTrace B m) = O pub B ch t := by
  apply congrArg roundInclusion
  funext j i
  apply congrArg (fun f : PointFunction K => (rounds ch j f).coeff i.val)
  funext a
  rw [terminal_add_pure]

/-- Common slope: independent of the honest instance and all of N. -/
def pureLinear (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : M K F →ₗ[F] Payload K :=
  ((L π B ch).restrictScalars F).comp (pureTrace B)

theorem M_pure (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (m : M K F) (n : N K F) :
    payload π pub B t ch (m,n) = payload π pub B t ch (0,n) + pureLinear π B ch m := by
  simp only [payload, run_split]
  change L π B ch (actual pub B t ch (m,n)) + O pub B ch (actual pub B t ch (m,n)) =
    L π B ch (actual pub B t ch (0,n)) + O pub B ch (actual pub B t ch (0,n)) + _
  rw [actual_add_pure, map_add, O_add_pure]
  change _ = _ + L π B ch (pureTrace B m)
  abel

#print axioms run_split
#print axioms terminal_add_pure
#print axioms M_pure
end R0Z.PayloadSplit
