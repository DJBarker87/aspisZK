import S9KappaFinReadConsumerV1
import S9PairingOpaqueInterfaceV1
set_option autoImplicit false
noncomputable section
namespace AspisR1S9SevenFoldAssemblyV1
open AspisR1S9KappaFinSevenV1 (partAt W)
open AspisR1S9ActualFinalSumV1 (A)
open AspisR1S9ActualKappaFinalSumV1 (kappaPolynomial)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode)
open AspisR1S9PairingOpaqueInterfaceV1 (foldValue pairingValue)
abbrev E := AspisWideTower.WideExact

/-- All seven meanings are consumed on the same source array. The generic
pairing operator is an explicit definition, not an assumed implementation law. -/
theorem kappa_polynomial_eq_pairing (parts : A) (kappa : W)
    (raw : Fin 7 → Fin 1024 → E) (a0 a1 : E) (f : Fin 64 → E)
    (hvalues : ∀ i,decode (partAt parts i)=foldValue (raw i) a0 a1 f) :
    kappaPolynomial parts kappa=pairingValue raw (decode kappa) a0 a1 f := by
  have hs := AspisR1S9KappaFinReadConsumerV1.kappaPolynomial_eq_fin_values
    parts kappa (fun i => foldValue (raw i) a0 a1 f) hvalues
  have hop := AspisR1S9PairingOpaqueInterfaceV1.polynomial_operator_eq
    (decode kappa) (fun i => foldValue (raw i) a0 a1 f)
  have hm := AspisR1S9PairingOpaqueInterfaceV1.field_polynomial_fold raw (decode kappa) a0 a1 f
  exact hs.trans (hop.trans hm)

#print axioms kappa_polynomial_eq_pairing
end AspisR1S9SevenFoldAssemblyV1
end
