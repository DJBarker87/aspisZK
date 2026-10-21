import S3PowersCanonicalTraceV1
import CurrentPowersExactProduct
import PowersP6IndexedOutputV1
import S3S9CurrentFieldOpsV1
import S3S9TransparentFoldS2InstanceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S3PowersToS9ScalarJoinV1

abbrev PowerWide := AspisR1PowersConcreteMul.CallbackWide
abbrev S9Wide := AspisR1S9CurrentFieldOpsV1.S
abbrev ExactWide := AspisR1CurrentWide.Proof.E
abbrev S2Exact := AspisR1S9TransparentFoldS2InstanceV1.E

/-- Map the retained current-powers callback carrier into the nominal helper
carrier used by the scalar-factor source cut. The map is through the shared
eight-coordinate current-wide representation. -/
def powerToS9Helper (x : PowerWide) : S9Wide :=
  AspisR1S9CurrentFieldOpsV1.fromE (AspisR1PowersExactProduct.toFull x)

def helperPowersArray (values : List PowerWide)
    (hvalues : values.length = (4#usize).val) : Array S9Wide (4#usize) :=
  ⟨values.map powerToS9Helper, by
    rw [List.length_map, hvalues]⟩

theorem powerToS9Helper_toE (x : PowerWide) :
    AspisR1S9CurrentFieldOpsV1.toE (powerToS9Helper x) =
      AspisR1PowersExactProduct.toFull x := by
  exact AspisR1S9CurrentFieldOpsV1.to_from _

theorem powerToS9Helper_canonical (x : PowerWide)
    (hx : AspisR1PowersConcreteMul.Canonical x) :
    AspisR1S9CurrentFieldOpsV1.Canonical (powerToS9Helper x) := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9CurrentFieldOpsV1.toE (powerToS9Helper x))
  rw [powerToS9Helper_toE]
  exact hx

theorem powerToS9Helper_decode (x : PowerWide) :
    AspisR1S9CurrentFieldOpsV1.decode (powerToS9Helper x) =
      AspisR1PowersExactProduct.decode x := by
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9CurrentFieldOpsV1.toE (powerToS9Helper x)) = _
  rw [powerToS9Helper_toE]
  rfl

/-- Every successful four-step retained powers trace yields scalar-factor
helper values with the same indexed power meaning. The Rust `from_fn`
correspondence and the caller assignment `ap0 := powers(alpha[0])` remain
outside this trace theorem. -/
theorem powers_trace_to_s9_helper_values
    (x : PowerWide) (values : List PowerWide)
    (final : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final)) :
    ∀ i, i < 4 → ∃ helperValue,
      (values[i]?).map powerToS9Helper = some helperValue ∧
      AspisR1S9CurrentFieldOpsV1.Canonical helperValue ∧
      AspisR1S9CurrentFieldOpsV1.decode helperValue =
        AspisR1PowersExactProduct.decode x ^ i := by
  intro i hi
  have hfour : (4#usize).val = 4 := by decide
  have hi' : i < (4#usize).val := by simpa [hfour] using hi
  obtain ⟨value, hvalue, hcan, hdecode⟩ :=
    AspisR1PowersP6IndexedOutputV1.powersN_model_success_indexed
      (N := 4#usize) x values final hx hrun i hi'
  refine ⟨powerToS9Helper value, ?_, ?_, ?_⟩
  · simpa [hvalue]
  · exact powerToS9Helper_canonical value hcan
  · rw [powerToS9Helper_decode, hdecode]

/-- Compose the retained powers trace with the checked scalar-factor/S9
consumer. The helper input array is explicitly the mapped output list from
the same successful N=4 powers trace; this removes the free canonical-p-array
premise from the scalar-factor theorem. The caller equation identifying an
enclosing `ap0` with this array is still explicit outside this theorem. -/
theorem mapped_power_array_index_canonical
    (x : PowerWide) (values : List PowerWide)
    (final : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final))
    (p : Array S9Wide (4#usize))
    (hmap : p.val = values.map powerToS9Helper) :
    ∀ (index : Std.Usize) (y : S9Wide),
      Array.index_usize p index = .ok y →
        AspisR1S9CurrentFieldOpsV1.Canonical y := by
  obtain ⟨hlen, _hall, _hfinal⟩ :=
    AspisR1S3PowersCanonicalTraceV1.powersN_model_success
      (N := 4#usize) x values final hx hrun
  intro index y hread
  cases hopt : p[index]? with
  | none =>
      simp only [Aeneas.Std.Array.index_usize, hopt] at hread
      cases hread
  | some value =>
      have hy : value = y := by
        simp only [Aeneas.Std.Array.index_usize, hopt] at hread
        exact Result.ok.inj hread
      subst y
      have hmapread : (values.map powerToS9Helper)[index.val]? = some value := by
        change p.val[index.val]? = some value at hopt
        rw [hmap] at hopt
        exact hopt
      obtain ⟨hbound, _hget⟩ := List.getElem?_eq_some_iff.mp hmapread
      have hfour : (4#usize).val = 4 := by decide
      have hbound4 : index.val < 4 := by
        simpa [List.length_map, hlen, hfour] using hbound
      obtain ⟨helper, hhelper, hcan, _hdecode⟩ :=
        powers_trace_to_s9_helper_values x values final hx hrun
          index.val hbound4
      have heq : helper = value := Option.some.inj
        (hhelper.symm.trans (by simpa using hmapread))
      rw [← heq]
      exact hcan

abbrev ScalarFactorS9Conclusion
    (p : Array S9Wide (4#usize))
    (f : Array AspisR1S9HelperP6.field.QM31 (4#usize))
    (out : S9Wide) (seed : AspisR1S9HelperP6.field.QM31)
    (b : Fin 4 → S2Exact) (challenge1 : S2Exact) (j : Fin 4) : Prop :=
  ∃ (j0 j1 j2 j3 : Std.Usize) (p0 p1 p2 p3 : S9Wide)
    (q0 q1 q2 q3 : AspisR1S9HelperP6.field.QM31),
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
      AspisR1.S2LibraFactoredIdentity.scalar
        (AspisR1.S2LibraFactoredIdentity.scaled
          (AspisR1S9TransparentFoldS2InstanceV1.readVector
            (AspisR1S9CurrentFieldOpsV1.decode p0)
            (AspisR1S9CurrentFieldOpsV1.decode p3)
            (AspisR1S9CurrentFieldOpsV1.decode p2)
            (AspisR1S9CurrentFieldOpsV1.decode p1))
          (AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER))
        (algebraMap AspisR1S9TransparentFoldS2InstanceV1.ExactQM
          AspisR1S9TransparentFoldS2InstanceV1.E
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) ∧
    AspisR1.S3S9CurrentSourceModel.oldS9Weight
        (AspisR1S9TransparentFoldS2InstanceV1.readVector
          (AspisR1S9CurrentFieldOpsV1.decode p0)
          (AspisR1S9CurrentFieldOpsV1.decode p3)
          (AspisR1S9CurrentFieldOpsV1.decode p2)
          (AspisR1S9CurrentFieldOpsV1.decode p1)) b
        (AspisR1CurrentWide.Proof.wideScalarEmbedding
          AspisR1S9HelperP6.weights.QUARTER)
        (algebraMap AspisR1S9TransparentFoldS2InstanceV1.ExactQM
          AspisR1S9TransparentFoldS2InstanceV1.E
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) challenge1 j =
      AspisR1.S2LibraFactoredIdentity.factored
        (AspisR1.S2LibraFactoredIdentity.scaled
          (AspisR1S9TransparentFoldS2InstanceV1.readVector
            (AspisR1S9CurrentFieldOpsV1.decode p0)
            (AspisR1S9CurrentFieldOpsV1.decode p3)
            (AspisR1S9CurrentFieldOpsV1.decode p2)
            (AspisR1S9CurrentFieldOpsV1.decode p1))
          (AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER))
        (AspisR1.S2LibraFactoredIdentity.scaled b
          (AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER))
        (algebraMap AspisR1S9TransparentFoldS2InstanceV1.ExactQM
          AspisR1S9TransparentFoldS2InstanceV1.E
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))) challenge1 j

theorem scalar_factor_on_powers_trace_with_s9_instance
    (ops : AspisR1S9HelperP6.FieldOps)
    (x : PowerWide) (values : List PowerWide)
    (final : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final))
    (p : Array S9Wide (4#usize))
    (hmap : p.val = values.map powerToS9Helper)
    (seed : AspisR1S9HelperP6.field.QM31)
    (f : Array AspisR1S9HelperP6.field.QM31 (4#usize))
    (out : S9Wide)
    (b : Fin 4 → S2Exact) (challenge1 : S2Exact) (j : Fin 4)
    (hscalar : (letI : AspisR1S9TransparentFoldActualOpsConsumerV1.Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      (4#usize) seed = .ok f) :
    ScalarFactorS9Conclusion p f out seed b challenge1 j := by
  exact AspisR1S9TransparentFoldS2InstanceV1.scalar_factor_success_with_s9_model_instance
    ops p f out seed b challenge1 j hscalar
    (mapped_power_array_index_canonical x values final hx hrun p hmap)
    hseed hpowers

#print axioms powerToS9Helper_toE
#print axioms powerToS9Helper_canonical
#print axioms powerToS9Helper_decode
#print axioms powers_trace_to_s9_helper_values
#print axioms mapped_power_array_index_canonical
#print axioms scalar_factor_on_powers_trace_with_s9_instance

end AspisR1S3PowersToS9ScalarJoinV1
