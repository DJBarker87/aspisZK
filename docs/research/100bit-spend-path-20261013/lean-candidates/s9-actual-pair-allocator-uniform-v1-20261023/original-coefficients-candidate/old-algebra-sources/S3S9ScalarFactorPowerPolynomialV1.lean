import S3S9ScalarFactorPowerArrayMeaningV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorPowerPolynomialV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev E := AspisWideTower.WideExact

def powerTerm (p : S) (seed : ExactQM) (n : Nat) : E :=
  ⟨AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM p.c0) * seed ^ n,
   AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM p.c1) * seed ^ n⟩

/-- Scalar-factor's four reads, followed by the quarter scaling, with the
same `p[i]` values selected through `PERM[i]`.  The first term is written as
`p0`; the remaining terms are its componentwise products by seed, seed² and
seed³.  This is an output equation for the emitted helper under the explicit
P6 iterator-fold law; it does not identify the surrounding `Weights::pair`
caller or discharge the source/Std `from_fn` correspondence. -/
theorem scalar_factor_kpowers_four_term_polynomial
    (ops : Ops) (p : Array S 4#usize) (f : Array Q 4#usize) (out : S)
    (seed : Q)
    (hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops))
    (hscalar : (letI : Ops :=
      AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hzeroCan : AspisR1S9ScalarFactorFourFoldMeaningV1.CanonicalS
      AspisR1S9HelperP6.field.WideExact.ZERO)
    (hzeroDecode : AspisR1S9ScalarFactorFourFoldMeaningV1.DecodeS
      AspisR1S9HelperP6.field.WideExact.ZERO = 0)
    (hpvalues : ∀ (index : U) (x : S),
      Array.index_usize p index = .ok x →
        AspisR1S9ScalarFactorFourFoldMeaningV1.CanonicalS x)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      (4#usize) seed = .ok f) :
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
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE out) =
        (((AspisR1CurrentWide.Proof.decodeWide
              (AspisR1S9CurrentFieldOpsV1.toE p0) +
            powerTerm p1 (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 1) +
          powerTerm p2 (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 2) +
        powerTerm p3 (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 3) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q0) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 0 ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q1) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 1 ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q2) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 2 ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q3) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 3 := by
  obtain ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1, q2, q3,
    hcan, hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2,
    hperm3, hp3, hq3, hvalue⟩ :=
    AspisR1S9ScalarFactorKpowersReadV1.scalar_factor_kpowers_four_term_meaning
      ops p f out seed hfold hscalar hzeroCan hzeroDecode hpvalues hseed hpowers
  have hpq0 := AspisR1S9ScalarFactorPowerArrayMeaningV1.kpowers_array_read_power_value
    seed f hseed hpowers 0#usize q0 hq0
  have hpq1 := AspisR1S9ScalarFactorPowerArrayMeaningV1.kpowers_array_read_power_value
    seed f hseed hpowers 1#usize q1 hq1
  have hpq2 := AspisR1S9ScalarFactorPowerArrayMeaningV1.kpowers_array_read_power_value
    seed f hseed hpowers 2#usize q2 hq2
  have hpq3 := AspisR1S9ScalarFactorPowerArrayMeaningV1.kpowers_array_read_power_value
    seed f hseed hpowers 3#usize q3 hq3
  have hpq0' : AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q0) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 0 := by
    simpa [AspisR1S9GeneratedWideMulQM31V2.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hpq0
  have hpq1' : AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q1) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 1 := by
    simpa [AspisR1S9GeneratedWideMulQM31V2.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hpq1
  have hpq2' : AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q2) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 2 := by
    simpa [AspisR1S9GeneratedWideMulQM31V2.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hpq2
  have hpq3' : AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q3) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 3 := by
    simpa [AspisR1S9GeneratedWideMulQM31V2.toQM,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hpq3
  have hterm0 : AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p0 q0 =
      AspisR1S9CurrentFieldOpsV1.decode p0 := by
    change (⟨AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p0.c0) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q0),
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p0.c1) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q0)⟩ : E) =
      (⟨AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p0.c0),
        AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p0.c1)⟩ : E)
    rw [hpq0']
    simp only [pow_zero, mul_one]
  have hterm1 : AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p1 q1 =
      powerTerm p1 (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 1 := by
    change (⟨AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p1.c0) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q1),
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p1.c1) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q1)⟩ : E) =
      (⟨AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p1.c0) *
            AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 1,
        AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p1.c1) *
            AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 1⟩ : E)
    rw [hpq1']
  have hterm2 : AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p2 q2 =
      powerTerm p2 (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 2 := by
    change (⟨AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p2.c0) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q2),
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p2.c1) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q2)⟩ : E) =
      (⟨AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p2.c0) *
            AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 2,
        AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p2.c1) *
            AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 2⟩ : E)
    rw [hpq2']
  have hterm3 : AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p3 q3 =
      powerTerm p3 (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 3 := by
    change (⟨AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p3.c0) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q3),
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM p3.c1) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q3)⟩ : E) =
      (⟨AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p3.c0) *
            AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 3,
        AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM p3.c1) *
            AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 3⟩ : E)
    rw [hpq3']
  refine ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1, q2, q3,
    hcan, hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2,
    hperm3, hp3, hq3, ?_, hpq0, hpq1, hpq2, hpq3⟩
  rw [hvalue, hterm0, hterm1, hterm2, hterm3]
  simp [AspisR1S9CurrentFieldOpsV1.decode,
    AspisR1S9CurrentFieldOpsV1.toE]

#print axioms scalar_factor_kpowers_four_term_polynomial

end AspisR1S9ScalarFactorPowerPolynomialV1
