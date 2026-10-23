import S9NativeScalarTermOrdinaryV1
import S9ActualIndexedPowersSemanticsV1
import S9ActualPairPowersProducerV1
import S9SharedSumObservationsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ScalarActualPowerPolynomialV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeDecodedScalarProductV1
open AspisR1S9SharedSumObservationsV1 (scalarValue)
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev QCan := AspisR1S9ActualScalarFourTermMeaningV1.GoodQArray
abbrev Powers := Array NativeW 4#usize
abbrev Factors := Array NativeQ 4#usize
abbrev E := AspisWideTower.WideExact

def quarter : E := AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER

def scalarPolynomial (x : E) (f : Factors) : E :=
  (((((0 : E)+x^0*scalarValue f 0#usize)+x^3*scalarValue f 1#usize)+
    x^2*scalarValue f 2#usize)+x^1*scalarValue f 3#usize)*quarter

/-- SAME native powers4/scalar executions, actual PERM[0,3,2,1] and source
quarter. All source powers and coefficient reads are derived; no desired
power/term/scalar polynomial equation is assumed. -/
theorem actual_scalar_same_power_polynomial
    (f : Factors) (x : NativeW) (p : Powers) (out : NativeW)
    (hx : Can x) (hf : QCan f)
    (hpowers : weights.powers 4#usize x=.ok p)
    (hscalar : weights.Weights.scalar_factor f p=.ok out) :
    Can out ∧ decodeNative out=scalarPolynomial (decodeNative x) f := by
  have hpow := AspisR1S9ActualIndexedPowersSemanticsV1.actual_powers_four_success_decodes_powers
    x p hx hpowers
  have hp := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    x p hx hpowers
  obtain ⟨hout,p0,p1,p2,p3,q0,q1,q2,q3,hp0,hq0,hp1,hq1,hp2,hq2,hp3,hq3,hvalue⟩ :=
    AspisR1S9ActualScalarNativeReadsV1.actual_scalar_success_native_reads_quarter f p out hp hf hscalar
  have v0 := hpow 0#usize p0 hp0
  have v1 := hpow 3#usize p1 hp1
  have v2 := hpow 2#usize p2 hp2
  have v3 := hpow 1#usize p3 hp3
  have e0 : scalarEmbed q0=scalarValue f 0#usize := by unfold scalarValue; rw [hq0]
  have e1 : scalarEmbed q1=scalarValue f 1#usize := by unfold scalarValue; rw [hq1]
  have e2 : scalarEmbed q2=scalarValue f 2#usize := by unfold scalarValue; rw [hq2]
  have e3 : scalarEmbed q3=scalarValue f 3#usize := by unfold scalarValue; rw [hq3]
  change decodeNative out =
    (((((0 : E)+AspisR1S9ActualScalarNativeReadsV1.nativeTerm p0 q0)+
      AspisR1S9ActualScalarNativeReadsV1.nativeTerm p1 q1)+
      AspisR1S9ActualScalarNativeReadsV1.nativeTerm p2 q2)+
      AspisR1S9ActualScalarNativeReadsV1.nativeTerm p3 q3)*
        AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER at hvalue
  refine ⟨hout,?_⟩
  unfold scalarPolynomial quarter
  rw [hvalue,
    AspisR1S9NativeScalarTermOrdinaryV1.nativeTerm_eq_decoded_mul_embed p0 q0,
    AspisR1S9NativeScalarTermOrdinaryV1.nativeTerm_eq_decoded_mul_embed p1 q1,
    AspisR1S9NativeScalarTermOrdinaryV1.nativeTerm_eq_decoded_mul_embed p2 q2,
    AspisR1S9NativeScalarTermOrdinaryV1.nativeTerm_eq_decoded_mul_embed p3 q3,
    v0,v1,v2,v3,e0,e1,e2,e3]

#print axioms actual_scalar_same_power_polynomial
end AspisR1S9ScalarActualPowerPolynomialV1
