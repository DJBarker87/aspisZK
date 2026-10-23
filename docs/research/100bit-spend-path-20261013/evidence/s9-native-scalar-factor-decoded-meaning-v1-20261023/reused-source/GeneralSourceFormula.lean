import S3S9CurrentFieldOpsV1
import AspisR1S9HelperP6.Funs
import S2LibraFactoredIdentity
import S3S9CurrentSourceModel
import TransparentFoldActualOpsConsumerV1
import S3S9ScalarFactorPowerPolynomialV1
import KpowersP6PowerSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9TransparentFoldS2InstanceV1

abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev CanonicalS := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev DecodeS := AspisR1S9CurrentFieldOpsV1.decode
abbrev E := AspisWideTower.WideExact
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev U := Std.Usize

open AspisR1.S2LibraFactoredIdentity

theorem zero_canonical : CanonicalS AspisR1S9HelperP6.field.WideExact.ZERO := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9CurrentFieldOpsV1.toE AspisR1S9HelperP6.field.WideExact.ZERO)
  rw [show AspisR1S9CurrentFieldOpsV1.toE AspisR1S9HelperP6.field.WideExact.ZERO =
    AspisR1S9GeneratedWideMulQM31V2.toWide AspisR1S9HelperP6.field.WideExact.ZERO
      from by rfl]
  norm_num [AspisR1CurrentWide.Proof.CanonicalWide,
    AspisR1CurrentWide.Proof.CanonicalQM,
    AspisR1CurrentWide.Proof.toQM,
    AspisR1CurrentWide.Proof.toCM,
    AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.P,
    AspisR1.ExtractedCurrentM31AddSub.P,
    AspisR1S9GeneratedWideMulQM31V2.toWide,
    AspisR1S9GeneratedWideMulQM31V2.toQM,
    AspisR1S9HelperP6.field.WideExact.ZERO,
    AspisR1S9HelperP6.field.QM31.ZERO]

theorem zero_decode : DecodeS AspisR1S9HelperP6.field.WideExact.ZERO = 0 := by
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9CurrentFieldOpsV1.toE AspisR1S9HelperP6.field.WideExact.ZERO) = 0
  rw [show AspisR1S9CurrentFieldOpsV1.toE AspisR1S9HelperP6.field.WideExact.ZERO =
    AspisR1S9GeneratedWideMulQM31V2.toWide AspisR1S9HelperP6.field.WideExact.ZERO
      from by rfl]
  apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals norm_num [AspisR1CurrentWide.Proof.decodeWide,
    AspisR1CurrentWide.Proof.decodeQM,
    AspisR1.ExtractedCurrentQM31Exact.decode,
    AspisR1S9GeneratedWideMulQM31V2.toWide,
    AspisR1S9GeneratedWideMulQM31V2.toQM,
    AspisR1CurrentWide.Proof.toQM,
    AspisR1CurrentWide.Proof.toCM,
    AspisR1S9HelperP6.field.WideExact.ZERO,
    AspisR1S9HelperP6.field.QM31.ZERO]

theorem perm_reads :
    Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok 0#usize ∧
    Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok 3#usize ∧
    Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok 2#usize ∧
    Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok 1#usize := by
  norm_num [AspisR1S9HelperP6.weights.PERM, Array.make,
    Array.index_usize]

def readVector (x0 x1 x2 x3 : E) : Fin 4 → E := fun i =>
  if i.val = 0 then x0 else if i.val = 1 then x1 else if i.val = 2 then x2 else x3

theorem readVector_perm (x0 x1 x2 x3 : E) :
    readVector x0 x3 x2 x1 (perm 0) = x0 ∧
    readVector x0 x3 x2 x1 (perm 1) = x1 ∧
    readVector x0 x3 x2 x1 (perm 2) = x2 ∧
    readVector x0 x3 x2 x1 (perm 3) = x3 := by
  norm_num [readVector, perm]

private theorem powerTerm_eq_algebraMap_mul (p : S) (seed : ExactQM) (n : Nat) :
    AspisR1S9ScalarFactorPowerPolynomialV1.powerTerm p seed n =
      AspisR1S9CurrentFieldOpsV1.decode p *
        (algebraMap ExactQM E seed) ^ n := by
  have hmap : AspisR1S9CurrentFieldOpsV1.toE p =
      AspisR1S9GeneratedWideMulQM31V2.toWide p := by
    cases p <;> rfl
  have hdecode : AspisR1S9CurrentFieldOpsV1.decode p =
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide p) := by
    change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE p) = _
    rw [hmap]
  rw [hdecode]
  rw [← map_pow (algebraMap ExactQM E) seed n]
  apply QuadraticAlgebra.ext <;>
    simp [AspisR1S9ScalarFactorPowerPolynomialV1.powerTerm,
      AspisR1S9GeneratedWideMulQM31V2.toWide,
      AspisR1S9GeneratedWideMulQM31V2.toQM,
      AspisR1CurrentWide.Proof.decodeWide,
      AspisR1CurrentWide.Proof.decodeQM,
      QuadraticAlgebra.algebraMap_eq]

/-- General installed scalar-factor meaning for arbitrary actual factor reads.
This is the leaf needed by normal `Weights::pair` rows, whose `f` vectors are
constructor-produced factors rather than geometric power arrays. -/
theorem scalar_factor_success_general_source_formula
    (ops : AspisR1S9HelperP6.FieldOps)
    (p : Array S (4#usize)) (f : Array Q (4#usize)) (out : S)
    (hscalar : (letI : AspisR1S9HelperP6.FieldOps := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hpvalues : ∀ (index : U) (x : S),
      Array.index_usize p index = .ok x → CanonicalS x)
    (hqvalues : ∀ (index : U) (x : Q),
      Array.index_usize f index = .ok x →
        AspisR1CurrentWide.Proof.CanonicalQM
          (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)) :
    ∃ (we : S) (j0 j1 j2 j3 : U)
      (p0 p1 p2 p3 : S) (q0 q1 q2 q3 : Q),
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9CurrentFieldOpsV1.toE we) ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize p j0 = .ok p0 ∧ Array.index_usize f 0#usize = .ok q0 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize p j1 = .ok p1 ∧ Array.index_usize f 1#usize = .ok q1 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize p j2 = .ok p2 ∧ Array.index_usize f 2#usize = .ok q2 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize p j3 = .ok p3 ∧ Array.index_usize f 3#usize = .ok q3 ∧
      DecodeS out = (((((0 : E) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p0 q0) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p1 q1) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p2 q2) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p3 q3) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER := by
  have hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)) :=
    AspisR1S9TransparentFoldActualOpsConsumerV1.actualFactorOps_after_extractedFold_satisfies_P6 ops
  apply AspisR1S9ScalarFactorFourFoldMeaningV1.scalar_factor_success_four_term_meaning
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
    p f out hfold hscalar zero_canonical zero_decode hpvalues
  intro index x hread
  have hx := hqvalues index x hread
  simpa only [AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM,
    AspisR1S9GeneratedWideMulQM31V2.toQM] using hx

/-- The output polynomial is the S2 scalar term over the exact same four
source reads.  The local vector lists the source array in natural order,
while the emitted helper reads it through `[0,3,2,1]`; this explicit reindexing
is what makes `scalar_scaled` applicable. -/
theorem scalar_factor_success_is_s2_scalar
    (ops : AspisR1S9HelperP6.FieldOps)
    (p : Array S (4#usize)) (f : Array Q (4#usize)) (out : S) (seed : Q)
    (hscalar : (letI : AspisR1S9HelperP6.FieldOps := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hpvalues : ∀ (index : U) (x : S),
      Array.index_usize p index = .ok x → CanonicalS x)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps (4#usize) seed = .ok f) :
    ∃ (we : S) (j0 j1 j2 j3 : U) (p0 p1 p2 p3 : S) (q0 q1 q2 q3 : Q),
      Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize p j0 = .ok p0 ∧ Array.index_usize f 0#usize = .ok q0 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize p j1 = .ok p1 ∧ Array.index_usize f 1#usize = .ok q1 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize p j2 = .ok p2 ∧ Array.index_usize f 2#usize = .ok q2 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize p j3 = .ok p3 ∧ Array.index_usize f 3#usize = .ok q3 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE out) =
        scalar (scaled
          (readVector (AspisR1S9CurrentFieldOpsV1.decode p0)
            (AspisR1S9CurrentFieldOpsV1.decode p3)
            (AspisR1S9CurrentFieldOpsV1.decode p2)
            (AspisR1S9CurrentFieldOpsV1.decode p1))
          (AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER))
          (algebraMap ExactQM E
            (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) := by
  obtain ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1, q2, q3,
    _hcan, hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2,
    hperm3, hp3, hq3, hvalue, _hqv0, _hqv1, _hqv2, _hqv3⟩ :=
    AspisR1S9TransparentFoldActualOpsConsumerV1.scalar_factor_four_term_polynomial_from_extracted_fold
      ops p f out seed hscalar zero_canonical zero_decode hpvalues hseed hpowers
  refine ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1, q2, q3,
    hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2, hperm3, hp3, hq3,
    ?_⟩
  rw [hvalue, scalar_scaled]
  have hvec := readVector_perm
    (AspisR1S9CurrentFieldOpsV1.decode p0)
    (AspisR1S9CurrentFieldOpsV1.decode p1)
    (AspisR1S9CurrentFieldOpsV1.decode p2)
    (AspisR1S9CurrentFieldOpsV1.decode p3)
  rcases hvec with ⟨h0, h1, h2, h3⟩
  rw [h0, h1, h2, h3]
  rw [powerTerm_eq_algebraMap_mul, powerTerm_eq_algebraMap_mul,
    powerTerm_eq_algebraMap_mul]
  simp only [AspisR1S9CurrentFieldOpsV1.decode]
  ring_nf

/-- A successful source `scalar_factor` call and the retained old/factored S9
identity use the very same four decoded source reads.  This is the narrow
machine-to-model join for one Libra low factor; it does not claim that the
other terms or the enclosing `factored_s2_libra_weights` loop have run. -/
theorem scalar_factor_success_with_s9_model_instance
    (ops : AspisR1S9HelperP6.FieldOps)
    (p : Array S (4#usize)) (f : Array Q (4#usize)) (out : S) (seed : Q)
    (b : Fin 4 → E) (challenge1 : E) (j : Fin 4)
    (hscalar : (letI : AspisR1S9HelperP6.FieldOps := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hpvalues : ∀ (index : U) (x : S),
      Array.index_usize p index = .ok x → CanonicalS x)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps (4#usize) seed = .ok f) :
    ∃ (j0 j1 j2 j3 : U) (p0 p1 p2 p3 : S)
      (q0 q1 q2 q3 : Q),
      Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize p j0 = .ok p0 ∧ Array.index_usize f 0#usize = .ok q0 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize p j1 = .ok p1 ∧ Array.index_usize f 1#usize = .ok q1 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize p j2 = .ok p2 ∧ Array.index_usize f 2#usize = .ok q2 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize p j3 = .ok p3 ∧ Array.index_usize f 3#usize = .ok q3 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE out) =
        scalar
          (scaled
            (readVector (AspisR1S9CurrentFieldOpsV1.decode p0)
              (AspisR1S9CurrentFieldOpsV1.decode p3)
              (AspisR1S9CurrentFieldOpsV1.decode p2)
              (AspisR1S9CurrentFieldOpsV1.decode p1))
            (AspisR1CurrentWide.Proof.wideScalarEmbedding
              AspisR1S9HelperP6.weights.QUARTER))
          (algebraMap ExactQM E
            (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) ∧
      AspisR1.S3S9CurrentSourceModel.oldS9Weight
          (readVector (AspisR1S9CurrentFieldOpsV1.decode p0)
            (AspisR1S9CurrentFieldOpsV1.decode p3)
            (AspisR1S9CurrentFieldOpsV1.decode p2)
            (AspisR1S9CurrentFieldOpsV1.decode p1)) b
          (AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER)
          (algebraMap ExactQM E
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) challenge1 j =
        factored
          (scaled
            (readVector (AspisR1S9CurrentFieldOpsV1.decode p0)
              (AspisR1S9CurrentFieldOpsV1.decode p3)
              (AspisR1S9CurrentFieldOpsV1.decode p2)
              (AspisR1S9CurrentFieldOpsV1.decode p1))
            (AspisR1CurrentWide.Proof.wideScalarEmbedding
              AspisR1S9HelperP6.weights.QUARTER))
          (scaled b (AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER))
          (algebraMap ExactQM E
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) challenge1 j := by
  obtain ⟨_we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1', q2, q3,
    hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2,
    hperm3, hp3, hq3, hvalue⟩ :=
    scalar_factor_success_is_s2_scalar ops p f out seed hscalar hpvalues hseed hpowers
  refine ⟨j0, j1, j2, j3, p0, p1, p2, p3, q0, q1', q2, q3,
    hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2,
    hperm3, hp3, hq3, hvalue, ?_⟩
  exact AspisR1.S3S9CurrentSourceModel.old_s9_weight_eq_factored
    (readVector (AspisR1S9CurrentFieldOpsV1.decode p0)
      (AspisR1S9CurrentFieldOpsV1.decode p3)
      (AspisR1S9CurrentFieldOpsV1.decode p2)
      (AspisR1S9CurrentFieldOpsV1.decode p1)) b
    (AspisR1CurrentWide.Proof.wideScalarEmbedding
      AspisR1S9HelperP6.weights.QUARTER)
    (algebraMap ExactQM E
      (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) challenge1 j

#print axioms zero_canonical
#print axioms zero_decode
#print axioms perm_reads
#print axioms scalar_factor_success_general_source_formula
#print axioms scalar_factor_success_is_s2_scalar
#print axioms scalar_factor_success_with_s9_model_instance

end AspisR1S9TransparentFoldS2InstanceV1
