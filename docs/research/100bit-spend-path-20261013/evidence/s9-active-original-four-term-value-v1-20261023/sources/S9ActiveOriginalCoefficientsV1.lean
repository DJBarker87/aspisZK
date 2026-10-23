import S9ActualPairHelperOriginalCoefficientsV1
import S9ActualScalarFourTermMeaningV1
import S9NativeS3WeightBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActiveOriginalCoefficientsV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperW toHelperQ)
open AspisR1S9CandidateFoldMapPrimitivesV1 (mapArray)
abbrev A := Array W 4#usize
abbrev Q := aspis_core.field.QM31
abbrev Helper := AspisR1S9ActualPairHelperOriginalCoefficientsV1.WA

def cells (a : A) (j : Fin 4) : W := a.val[j.val]'(by simpa [a.property] using j.isLt)

theorem trace_decode_native (x : W) :
    AspisR1S9ActualPairHelperOriginalCoefficientsV1.TraceDecode (toHelperW x)=decode x := by
  calc
    AspisR1S9ActualPairHelperOriginalCoefficientsV1.TraceDecode (toHelperW x)=
        AspisR1S9CurrentFieldOpsV1.decode (toHelperW x) := by
      change AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide (toHelperW x))=
        AspisR1CurrentWide.Proof.decodeWide (AspisR1S9CurrentFieldOpsV1.toE (toHelperW x))
      rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    _ = _ := AspisR1S9ActualScalarFourTermMeaningV1.mapped_native_decode x

theorem mapped_helper_cells (a : A) (j : Fin 4) :
    AspisR1S9ActualPairHelperOriginalCoefficientsV1.cells (mapArray toHelperW a) j=
      toHelperW (cells a j) := by
  change (a.val.map toHelperW)[j.val]'_=toHelperW (a.val[j.val]'_)
  rw [List.getElem_map]

/-- SAME actual factored-helper output's four native decoded cells satisfy
the existing ORIGINAL S2 equations. No coefficient algebra is reproved and
no old helper run, coefficient meaning or desired output value is assumed. -/
theorem actual_helper_native_original_coefficients
    (ap0 ap1 : A) (extra : Array Q 2#usize) (libra : A)
    (hp0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0)
    (hp1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1)
    (he : ∀ i q,Array.index_usize extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (h : weights.factored_s2_libra_weights ap0 ap1 extra=.ok libra) :
    AspisR1S9ActualPairScalarCallbackV1.GoodArray libra ∧ ∃ q0 q1 : Q,
      Array.index_usize extra 0#usize=.ok q0 ∧ Array.index_usize extra 1#usize=.ok q1 ∧
      ∀ j : Fin 4,decode (cells libra j)=AspisR1.S2LibraFactoredIdentity.original
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase (mapArray toHelperW ap0))
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase (mapArray toHelperW ap1))
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1)) j := by
  obtain ⟨clibra,q0,q1,hq0,hq1,_,hvalue⟩ :=
    AspisR1S9ActualPairHelperOriginalCoefficientsV1.actual_helper_original_coefficients
      ap0 ap1 extra libra hp0 hp1 he h
  refine ⟨clibra,q0,q1,hq0,hq1,?_⟩
  intro j
  have hv := hvalue j
  rw [mapped_helper_cells,trace_decode_native] at hv
  exact hv

#print axioms trace_decode_native
#print axioms mapped_helper_cells
#print axioms actual_helper_native_original_coefficients
end AspisR1S9ActiveOriginalCoefficientsV1
