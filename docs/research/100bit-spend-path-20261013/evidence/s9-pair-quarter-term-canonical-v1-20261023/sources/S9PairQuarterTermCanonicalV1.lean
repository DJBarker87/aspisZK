import S9PairCallerStepOperationBridgeV1
import S9HighTermsTraceV1
import S9WideMulM31ConcreteTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairQuarterTermCanonicalV1

abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev HelperW := AspisR1S9HelperP6.field.WideExact
abbrev ScalarCutW := AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact

private def pairToScalarCutW (x : PairW) : ScalarCutW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

/-- The same successful quarter multiply that forms a term has canonical
output whenever its same-run mixed-product input is canonical. The proof uses
the retained actual mul_m31 total/canonical result and the caller operation
bridge; it does not assume term canonicality. -/
theorem pair_quarter_term_success_canonical
    (product : PairW) (term : PairW)
    (hproduct : AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W product))
    (hquarter : AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
      _root_.AspisR1S9PairCallerStepV1.weights.QUARTER = .ok term) :
    AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W term) := by
  let sourceInput : ScalarCutW := pairToScalarCutW product
  have hsourceToP6 :
      AspisR1S9WideMulM31ConcreteTotalV1.sourceToP6W sourceInput =
        AspisR1S9PairCallerStepV1.toP6W product := by
    cases product <;> rfl
  have hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9WideMulM31FullResultMapV1.mapWide sourceInput) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE
        (AspisR1S9WideMulM31ConcreteTotalV1.sourceToP6W sourceInput))
    rw [hsourceToP6]
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide
        (AspisR1S9PairCallerStepV1.toP6W product))
    exact hproduct
  obtain ⟨out,hout,houtCan,_houtDecode⟩ :=
    AspisR1S9WideMulM31ConcreteTotalV1.concrete_wide_mul_m31_total_exact
      sourceInput _root_.AspisR1S9PairCallerStepV1.weights.QUARTER hx
  have hpairMap := AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul_m31
    product _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
  rw [hquarter] at hpairMap
  rw [hsourceToP6] at hout
  have hhelper : @AspisR1S9HelperP6.FieldOps.wideMulM31
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6W product)
      (AspisR1S9PairCallerStepV1.toP6M
        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER) = .ok out := by
    simpa only [sourceInput, pairToScalarCutW,
      AspisR1S9PairCallerStepV1.toP6M] using hout
  change .ok (AspisR1S9PairCallerStepV1.toP6W term) =
    @AspisR1S9HelperP6.FieldOps.wideMulM31
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6W product)
      (AspisR1S9PairCallerStepV1.toP6M
        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER) at hpairMap
  rw [hhelper] at hpairMap
  have htermMap : AspisR1S9PairCallerStepV1.toP6W term = out := Result.ok.inj hpairMap
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9GeneratedWideMulQM31V2.toWide
      (AspisR1S9PairCallerStepV1.toP6W term))
  rw [htermMap]
  rw [← AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
  exact houtCan

#print axioms pair_quarter_term_success_canonical

end AspisR1S9PairQuarterTermCanonicalV1
