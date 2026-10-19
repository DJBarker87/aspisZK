import RawActualDecodeKTypedCoefficients
import RawSemanticCheckedStepPolynomialAdapter

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSemanticTypedPolynomialLift
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1.SemanticCoefficientCodec
open AspisWideTower

theorem polynomial_map {K L : Type} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (xs : List K) :
    (RawSemanticPolynomialOps.polynomial xs).map f =
      RawSemanticPolynomialOps.polynomial (xs.map f) := by
  induction xs with
  | nil => simp [RawSemanticPolynomialOps.polynomial]
  | cons x xs ih =>
      simp only [RawSemanticPolynomialOps.polynomial, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, List.map_cons, ih]

theorem polynomial_ofFn {K : Type} [CommSemiring K] (n : Nat) (xs : Fin n → K) :
    RawSemanticPolynomialOps.polynomial (List.ofFn xs) =
      ∑ i : Fin n, Polynomial.C (xs i) * Polynomial.X ^ i.val := by
  induction n with
  | zero => simp [RawSemanticPolynomialOps.polynomial]
  | succ n ih =>
      rw [List.ofFn_succ, RawSemanticPolynomialOps.polynomial, ih,
        Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring

theorem lowWide_eq_embedding (x : LowWide) :
    algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact WideExact x.val.re = x.val := by
  ext <;> simp [x.property]

theorem exactPolynomial_map_eq_typed
    (out : Array AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.MainQM 28#usize) (typed : Coefficients)
    (hvalues : ∀ j : Fin 28,
      AspisR1.ExtractedMaskQM31Exact.decode
        (mainToProbe (out.val[j.val]'(by simpa [out.property] using j.isLt))) =
          (typed j).val.re) :
    (exactPolynomial out).map
        (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact WideExact) =
      AspisR1.SemanticCoefficientCodec.polynomial typed := by
  have hlist :
      (mainArrayToProbe out).val.map AspisR1.ExtractedMaskQM31Exact.decode =
        List.ofFn (fun j : Fin 28 => (typed j).val.re) := by
    apply List.ext_getElem
    · simp [mainArrayToProbe, out.property]
    · intro i hi hj
      have hi28 : i < 28 := by simpa only [List.length_ofFn] using hj
      simpa only [mainArrayToProbe, List.getElem_map, List.getElem_ofFn]
        using hvalues ⟨i, hi28⟩
  unfold exactPolynomial
  rw [hlist, polynomial_map, List.map_ofFn]
  have hembed :
      (fun j : Fin 28 => algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact
        WideExact (typed j).val.re) = (fun j => (typed j).val) := by
    funext j
    exact lowWide_eq_embedding (typed j)
  change RawSemanticPolynomialOps.polynomial
    (List.ofFn (fun j : Fin 28 => algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact
      WideExact (typed j).val.re)) = _
  rw [hembed, polynomial_ofFn]
  rfl

theorem decodeMain_same_typed_polynomial
    (r : RawActualDecodeKMainAdapter.MainRecord)
    (out : Array AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.MainQM 28#usize)
    (h : RawActualDecodeKMainAdapter.decodeMain 28#usize r 0#usize = .ok (.Ok out))
    (hlen : (payload r).length = 896)
    (hstrict : ∀ j : Fin 28,
      AspisR1.ExtractedPrefixStrictPayload.StrictLowChunk
        (((payload r).drop (32*j.val)).take 32)) :
    ∃ typed : Coefficients,
      decodeCoefficients ((payload r).map AspisR1.ExtractedRecordByteValue.rawByte) = some typed ∧
      (exactPolynomial out).map
          (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact WideExact) =
        AspisR1.SemanticCoefficientCodec.polynomial typed := by
  obtain ⟨typed, hd, hv⟩ := decodeMain_coefficients_same_typed_payload r out h hlen hstrict
  exact ⟨typed, hd, exactPolynomial_map_eq_typed out typed hv⟩

#print axioms polynomial_map
#print axioms polynomial_ofFn
#print axioms lowWide_eq_embedding
#print axioms exactPolynomial_map_eq_typed
#print axioms decodeMain_same_typed_polynomial
end AspisR1PublicPreparation.RawSemanticTypedPolynomialLift
end
