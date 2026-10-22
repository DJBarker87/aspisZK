import S3S9ScalarFactorFourFoldMeaningV1
import KpowersCurrentQMSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorKpowersReadV1

abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize

private theorem index_success_bound {A : Type} {N : U} (a : Array A N)
    (i : U) (x : A) (h : Array.index_usize a i = .ok x) :
    i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

/-- A successful indexed read from the exact emitted `kpowers` array is
canonical under the installed CurrentWide QM semantics. This removes the
per-read canonicality premise for scalar_factor; the P6/Rust array-constructor
boundary remains in the kpowers owner. -/
theorem kpowers_success_read_current
    (seed : Q) (values : Array Q (4#usize))
    (hseed : AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.canonical seed)
    (hpowers : AspisR1S9HelperP6.weights.kpowers (4#usize) seed = .ok values)
    (index : U) (value : Q)
    (hread : Array.index_usize values index = .ok value) :
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.canonical value ∧
    AspisR1CurrentWide.Proof.decodeQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM value) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ index.val := by
  have hi := index_success_bound values index value hread
  have hget : values.val[index.val]? = some value := by
    unfold Array.index_usize at hread
    cases h : values[index]? with
    | none => simp [h] at hread
    | some y =>
        have hy : y = value := Result.ok.inj (by simpa [h] using hread)
        have hsome : values.val[index.val]? = some y := by simpa using h
        simpa [hy] using hsome
  exact AspisR1S9HelperP6PowerSemanticsV1.kpowers_success_pointwise
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics hseed hpowers
    index.val hi value hget

/-- Specialization of the four-step scalar-factor meaning theorem to an `f`
array returned by the actual selected `kpowers` helper. The caller still
supplies successful `kpowers` and canonical source seed, while scalar_factor's
P6 range-fold correspondence and `p`-array canonical reads remain explicit. -/
theorem scalar_factor_kpowers_four_term_meaning
    (ops : AspisR1S9HelperP6.FieldOps)
    (p : Array S 4#usize) (f : Array Q 4#usize) (out : S)
    (seed : Q)
    (hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops))
    (hscalar : (letI : AspisR1S9HelperP6.FieldOps :=
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
        (((((0 : AspisWideTower.WideExact) +
          AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p0 q0) +
          AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p1 q1) +
          AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p2 q2) +
          AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p3 q3) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER := by
  apply AspisR1S9ScalarFactorFourFoldMeaningV1.scalar_factor_success_four_term_meaning
    ops p f out hfold hscalar hzeroCan hzeroDecode hpvalues
  intro index value hread
  exact (kpowers_success_read_current seed f hseed hpowers index value hread).1

#print axioms kpowers_success_read_current
#print axioms scalar_factor_kpowers_four_term_meaning

end AspisR1S9ScalarFactorKpowersReadV1
