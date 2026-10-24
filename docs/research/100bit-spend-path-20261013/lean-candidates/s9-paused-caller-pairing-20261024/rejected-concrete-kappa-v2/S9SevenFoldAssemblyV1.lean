import S9KappaFinReadConsumerV1
import S9RawIdentityRowV1
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9SevenFoldAssemblyV1

open AspisR1S9KappaFinSevenV1 (partAt W)
open AspisR1S9ActualFinalSumV1 (A)
open AspisR1S9ActualKappaFinalSumV1 (kappaPolynomial)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode)
abbrev E := AspisWideTower.WideExact

/-- Consume explicit meanings of the SAME seven source parts. This theorem
adds no acceptance or public-row claim: those are supplied by the caller join. -/
theorem kappa_polynomial_eq_pairing (parts : A) (kappa : W)
    (raw : Fin 7 → Fin 1024 → E) (a0 a1 : E) (f : Fin 64 → E)
    (hvalues : ∀ i, decode (partAt parts i)=AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0 (raw i)))) :
    kappaPolynomial parts kappa=AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0
        (AspisR1.FunctionalWeights.weights
          (AspisR1.RawFunctionalWeights.rawFunctionals (RingHom.id E) raw)
          (AspisR1.RawFunctionalWeights.rawBaseFunctional (RingHom.id E) raw) (decode kappa)))) := by
  exact (AspisR1S9KappaFinReadConsumerV1.kappaPolynomial_eq_fin_values parts kappa
    (fun i => AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0 (raw i)))) hvalues).trans
    (AspisR1S9RawIdentityRowV1.sum_rows_eq_pairing raw (decode kappa) a0 a1 f)

#print axioms kappa_polynomial_eq_pairing
end AspisR1S9SevenFoldAssemblyV1
end
