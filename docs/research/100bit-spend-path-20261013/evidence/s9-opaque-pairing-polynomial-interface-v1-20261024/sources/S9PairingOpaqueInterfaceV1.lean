import S9RawIdentityRowV1
import S9PointOperatorTransportV1
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9PairingOpaqueInterfaceV1

def fieldPolynomial {E : Type} [Field E] (kappa : E) (v : Fin 7 → E) : E :=
  ∑ i : Fin 7,kappa^i.val*v i

def foldValue {E : Type} [Field E] (row : Fin 1024 → E)
    (a0 a1 : E) (f : Fin 64 → E) : E :=
  AspisR1.RoundPairing.dot f
    (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0 row))

def pairingValue {E : Type} [Field E] (raw : Fin 7 → Fin 1024 → E)
    (kappa a0 a1 : E) (f : Fin 64 → E) : E :=
  foldValue (AspisR1.FunctionalWeights.weights
    (AspisR1.RawFunctionalWeights.rawFunctionals (RingHom.id E) raw)
    (AspisR1.RawFunctionalWeights.rawBaseFunctional (RingHom.id E) raw) kappa) a0 a1 f

theorem field_polynomial_fold {E : Type} [Field E]
    (raw : Fin 7 → Fin 1024 → E) (kappa a0 a1 : E) (f : Fin 64 → E) :
    fieldPolynomial kappa (fun i => foldValue (raw i) a0 a1 f)=
      pairingValue raw kappa a0 a1 f :=
  AspisR1S9RawIdentityRowV1.sum_rows_eq_pairing raw kappa a0 a1 f

abbrev E := AspisWideTower.WideExact
open AspisR1S9WideMulOperatorBridgeV1 (fieldMul mul_operator_eq)
open AspisR1S9WideFieldOperatorBridgesV1 (fieldPow pow_operator_eq)
open AspisR1S9PointOperatorTransportV1 (fieldSum sum_operator_eq)

/-- Normalize operator dictionaries BEFORE source observations or seven
concrete row expressions are substituted. No finite sum is enumerated. -/
theorem polynomial_operator_eq (kappa : E) (v : Fin 7 → E) :
    (∑ i : Fin 7,kappa^i.val*v i)=fieldPolynomial kappa v := by
  have ht : (fun i : Fin 7 => kappa^i.val*v i)=
      (fun i : Fin 7 => fieldMul (fieldPow kappa i.val) (v i)) := by
    funext i
    exact (mul_operator_eq (kappa^i.val) (v i)).trans
      (congrArg (fun x : E => fieldMul x (v i)) (pow_operator_eq kappa i.val))
  exact (sum_operator_eq Finset.univ (fun i : Fin 7 => kappa^i.val*v i)).trans
    (congrArg (fieldSum Finset.univ) ht)

#print axioms field_polynomial_fold
#print axioms polynomial_operator_eq
end AspisR1S9PairingOpaqueInterfaceV1
end
