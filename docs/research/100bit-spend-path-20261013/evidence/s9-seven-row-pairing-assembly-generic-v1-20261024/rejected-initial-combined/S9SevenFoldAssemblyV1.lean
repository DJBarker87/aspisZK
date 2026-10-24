import S9KappaFinReadConsumerV1
import R1RawPairing
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9SevenFoldAssemblyV1

/-- Generic assembly of seven row values. The identity embedding is only an
algebraic interface; identification with the protocol's public rows is separate. -/
theorem sum_rows_eq_pairing {E : Type} [Field E]
    (raw : Fin 7 → Fin 1024 → E) (kappa a0 a1 : E) (f : Fin 64 → E) :
    (∑ i : Fin 7, kappa^i.val * AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0 (raw i)))) =
    AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0
        (AspisR1.FunctionalWeights.weights
          (AspisR1.RawFunctionalWeights.rawFunctionals (RingHom.id E) raw)
          (AspisR1.RawFunctionalWeights.rawBaseFunctional (RingHom.id E) raw) kappa))) := by
  simpa only [AspisR1.RawPairing.embeddedRow,RingHom.id_apply] using
    (AspisR1.RawPairing.two_dual_dot_eq_seven_rows (RingHom.id E) raw kappa a0 a1 f).symm

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
    (sum_rows_eq_pairing raw (decode kappa) a0 a1 f)

#print axioms sum_rows_eq_pairing
#print axioms kappa_polynomial_eq_pairing
end AspisR1S9SevenFoldAssemblyV1
end
