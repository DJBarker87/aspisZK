import AspisFormal.V8A100ScalarFingerprintGammaBound

/-!
# V8-A100 conditional raw-security arithmetic

This leaf checks exact rational arithmetic for the proposed direct schedule.
It deliberately does **not** claim the missing source composition theorem.
The current V7 compiler theorem parameterises the first-run SHA cap `Q` and
fork cap `R`; the concrete values below are therefore named a research
envelope, not a deployed certificate.  No proof-of-work divisor occurs.
-/

set_option autoImplicit false

namespace AspisV8A100RawSecurityLedger

def P : Nat := 2147483647
def fieldCardinality : Nat := P ^ 4
def nonzeroFieldCardinality : Nat := fieldCardinality - 1
def secureCircleParameterCardinality : Nat := P ^ 4 - P ^ 2

def researchQ : Nat := 2 ^ 36
def researchR : Nat := 259
def verifierFull256CallCap : Nat := 1511

def unifiedFreshExposureCap : Nat :=
  researchQ + verifierFull256CallCap +
    researchR * (researchQ + verifierFull256CallCap) + 2 * researchR

def globalFull256CallCap : Nat :=
  researchQ + verifierFull256CallCap +
    researchR * (2 * researchQ + verifierFull256CallCap)

/-! The pair count is kept as an exceptional closed-form cell.  Unfolding
`Nat.choose` at the 14-digit exposure cap builds a pathological recurrence
graph; `unified_exposure_pairs_exact` connects this literal to the symbolic
quantity without that reduction. -/
def unifiedExposurePairs : Nat := 159615994149495035121971953

def compilerNumerator : Nat :=
  unifiedFreshExposureCap + unifiedExposurePairs +
    unifiedFreshExposureCap * globalFull256CallCap

def queryNumerator : Nat → Nat
  | 21 => 7393662592209655999935020464195592148015408824055793636796803085
  | 22 => 3204816658150512709790016143025871214703406297554365823658832464480
  | 23 => 1328605514585440812515121909728334001399868654225255570808129023861600
  | 24 => 527788540669066362771632178639580682056097822890982775503529254729020600
  | _ => 0

def queryDenominator : Nat → Nat
  | 21 => 12040555749690594749239388146893137795143052287348718934096354265441751632206066179015265484800
  | 22 => 143459390671643080338858006328548634467103740668941284234642666778199466504034122047364474303283200
  | 23 => 1634950539201409891503571231950079354947224639635835969832739352227617415607410093013011771014139084800
  | 24 => 17856452928583865090450316453749447941588394573582706677021977989385637691517914207944319101249881293619200
  | _ => 1

def queryError (q : Nat) : ℚ :=
  (queryNumerator q : ℚ) / queryDenominator q

/-- `3 + q + 18 + 396430 + 100*28`, over nonzero QM31.  The last
term is the conservative scalar-DEEP family bound: the verifier checks two
gamma dots, so each of at most 100 nonmatching tuples contributes at most 28
roots. -/
def algebraicError (q : Nat) : ℚ :=
  ((3 + q + 18 + 396430 + 100 * 28 : Nat) : ℚ) /
    nonzeroFieldCardinality

/-- `100^2 * 1024^2` ordered-pair collision bound. -/
def twoPointTupleCollisionError : ℚ :=
  (10485760000 : ℚ) /
    (secureCircleParameterCardinality *
      (secureCircleParameterCardinality - 1))

def k12Error (q digestBits : Nat) : ℚ :=
  ((verifierFull256CallCap * (2 * q) +
      unifiedExposurePairs : Nat) : ℚ) / 2 ^ digestBits

def compilerError : ℚ := (compilerNumerator : ℚ) / 2 ^ 256

def conditionalRawError (q digestBits : Nat) : ℚ :=
  queryError q + algebraicError q + twoPointTupleCollisionError +
    k12Error q digestBits + compilerError

/-- The concrete scalar-DEEP theorem which licenses the `100 * 28` ledger
numerator.  Keeping this bridge in the arithmetic leaf prevents the displayed
constant from drifting away from the actual fixed width-29 family theorem. -/
theorem fixed_family_scalar_deep_fits_ledger_numerator
    (decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      AspisV5ComponentCQM31TowerExact.QM31Exact)
    (lanes : AspisPool.V7Width29ComponentExtraction.Width29InitialWords
      AspisV5ComponentCQM31TowerExact.QM31Exact)
    (parameter0 parameter1 : AspisV5ComponentCQM31TowerExact.QM31Exact)
    (public0 public1 : Fin 29 →
      AspisV5ComponentCQM31TowerExact.QM31Exact) :
    (AspisV8A100ScalarFingerprintGammaBound.nonmatchingTupleScalarGammaSet
      (AspisPool.V7FixedWidth29TupleList.fixedWidth29TupleList decoder lanes)
      parameter0 parameter1 public0 public1).card ≤ 100 * 28 := by
  exact AspisV8A100ScalarFingerprintGammaBound.fixedWidth29_nonmatching_scalar_gamma_card_le_2800
      decoder lanes parameter0 parameter1 public0 public1

theorem unified_exposure_pairs_exact :
    unifiedFreshExposureCap.choose 2 = unifiedExposurePairs := by
  rw [Nat.choose_two_right]
  norm_num [unifiedFreshExposureCap, unifiedExposurePairs, researchQ,
    researchR, verifierFull256CallCap]

theorem research_resource_envelope_exact :
    unifiedFreshExposureCap = 17867064344738 ∧
      globalFull256CallCap = 35665408818844 ∧
      compilerNumerator = 796852148397184761592959563 := by
  norm_num [unifiedFreshExposureCap, globalFull256CallCap, unifiedExposurePairs,
    compilerNumerator, researchQ, researchR, verifierFull256CallCap]

theorem visible_honest_work_fits_researchQ :
    2 ^ 35 + 2 ^ 31 + 2 ^ 34 < researchQ := by
  norm_num [researchQ]

theorem q21_digest208_conditional_raw_error_le_two_pow_neg100 :
    conditionalRawError 21 208 ≤ (1 : ℚ) / 2 ^ 100 := by
  norm_num [conditionalRawError, queryError, queryNumerator,
    queryDenominator, algebraicError, twoPointTupleCollisionError, k12Error,
    compilerError, nonzeroFieldCardinality, secureCircleParameterCardinality,
    fieldCardinality, P, unifiedFreshExposureCap, globalFull256CallCap,
    compilerNumerator, unifiedExposurePairs, researchQ, researchR,
    verifierFull256CallCap]

theorem q22_digest208_conditional_raw_error_le_two_pow_neg104 :
    conditionalRawError 22 208 ≤ (1 : ℚ) / 2 ^ 104 := by
  norm_num [conditionalRawError, queryError, queryNumerator,
    queryDenominator, algebraicError, twoPointTupleCollisionError, k12Error,
    compilerError, nonzeroFieldCardinality, secureCircleParameterCardinality,
    fieldCardinality, P, unifiedFreshExposureCap, globalFull256CallCap,
    compilerNumerator, unifiedExposurePairs, researchQ, researchR,
    verifierFull256CallCap]

theorem q22_digest208_conditional_raw_error_not_le_two_pow_neg105 :
    ¬ conditionalRawError 22 208 ≤ (1 : ℚ) / 2 ^ 105 := by
  norm_num [conditionalRawError, queryError, queryNumerator,
    queryDenominator, algebraicError, twoPointTupleCollisionError, k12Error,
    compilerError, nonzeroFieldCardinality, secureCircleParameterCardinality,
    fieldCardinality, P, unifiedFreshExposureCap, globalFull256CallCap,
    compilerNumerator, unifiedExposurePairs, researchQ, researchR,
    verifierFull256CallCap]

theorem q23_digest208_conditional_raw_error_le_two_pow_neg105 :
    conditionalRawError 23 208 ≤ (1 : ℚ) / 2 ^ 105 := by
  norm_num [conditionalRawError, queryError, queryNumerator,
    queryDenominator, algebraicError, twoPointTupleCollisionError, k12Error,
    compilerError, nonzeroFieldCardinality, secureCircleParameterCardinality,
    fieldCardinality, P, unifiedFreshExposureCap, globalFull256CallCap,
    compilerNumerator, unifiedExposurePairs, researchQ, researchR,
    verifierFull256CallCap]

#print axioms research_resource_envelope_exact
#print axioms unified_exposure_pairs_exact
#print axioms visible_honest_work_fits_researchQ
#print axioms fixed_family_scalar_deep_fits_ledger_numerator
#print axioms q21_digest208_conditional_raw_error_le_two_pow_neg100
#print axioms q22_digest208_conditional_raw_error_le_two_pow_neg104
#print axioms q22_digest208_conditional_raw_error_not_le_two_pow_neg105
#print axioms q23_digest208_conditional_raw_error_le_two_pow_neg105

end AspisV8A100RawSecurityLedger
