import S9ScalarActualPowerPolynomialV1
import S9SharedScalarModelValuesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ScalarConstructorModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9ScalarActualPowerPolynomialV1 (Can Powers)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
abbrev E := AspisWideTower.WideExact
abbrev Coeffs := Array NativeQ 4#usize

def factorPolynomial (x : E) (row : Nat → ExactQM) : E :=
  (((((0 : E)+x^0*embedQ (row 0))+x^3*embedQ (row 1))+
    x^2*embedQ (row 2))+x^1*embedQ (row 3))*
    AspisR1S9ScalarActualPowerPolynomialV1.quarter

/-- Actual powers/scalar success and the SAME source receiver row determine
its factor polynomial. Canonical source coefficients and all four model
values follow from receiver canonicality/table meaning, not scalar premises. -/
theorem actual_scalar_constructor_model
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (k d : Usize) (hk : k.val<5) (hd : d.val<5)
    (row : Row) (coeffs : Coeffs)
    (hr : Array.index_usize (fromCtor w).factors k=.ok row)
    (hcell : Array.index_usize row d=.ok coeffs)
    (x : NativeW) (p : Powers) (out : NativeW) (hx : Can x)
    (hp : weights.powers 4#usize x=.ok p)
    (hs : weights.Weights.scalar_factor coeffs p=.ok out) :
    Can out ∧ decodeNative out=factorPolynomial (decodeNative x) (model k.val d.val) := by
  have hq : AspisR1S9ScalarActualPowerPolynomialV1.QCan coeffs := by
    intro i q hi
    exact hc k d row coeffs i q hr hcell hi
  obtain ⟨hout,hval⟩ :=
    AspisR1S9ScalarActualPowerPolynomialV1.actual_scalar_same_power_polynomial
      coeffs x p out hx hq hp hs
  have hv := factor_scalar_values_model w model hm k d hk hd row coeffs hr hcell
  have v0 := hv (0 : Fin 4)
  have v1 := hv (1 : Fin 4)
  have v2 := hv (2 : Fin 4)
  have v3 := hv (3 : Fin 4)
  change scalarValue coeffs 0#usize = embedQ (model k.val d.val 0) at v0
  change scalarValue coeffs 1#usize = embedQ (model k.val d.val 1) at v1
  change scalarValue coeffs 2#usize = embedQ (model k.val d.val 2) at v2
  change scalarValue coeffs 3#usize = embedQ (model k.val d.val 3) at v3
  refine ⟨hout,?_⟩
  rw [hval]
  unfold AspisR1S9ScalarActualPowerPolynomialV1.scalarPolynomial factorPolynomial
  rw [v0,v1,v2,v3]

#print axioms actual_scalar_constructor_model
end AspisR1S9ScalarConstructorModelV1
