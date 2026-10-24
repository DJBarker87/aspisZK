import R1RawPairing
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9RawIdentityRowV1
variable {E : Type} [Field E]
theorem embedded_identity {n : Nat} (raw : Fin n → E) :
    AspisR1.RawPairing.embeddedRow (RingHom.id E) raw = raw := by
  funext i
  rfl

theorem sum_rows_eq_pairing
    (raw : Fin 7 → Fin 1024 → E) (kappa a0 a1 : E) (f : Fin 64 → E) :
    (∑ i : Fin 7, kappa^i.val * AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0 (raw i)))) =
    AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0
        (AspisR1.FunctionalWeights.weights
          (AspisR1.RawFunctionalWeights.rawFunctionals (RingHom.id E) raw)
          (AspisR1.RawFunctionalWeights.rawBaseFunctional (RingHom.id E) raw) kappa))) := by
  have h := (AspisR1.RawPairing.two_dual_dot_eq_seven_rows (RingHom.id E) raw kappa a0 a1 f).symm
  simp only [embedded_identity] at h
  exact h
#print axioms embedded_identity
#print axioms sum_rows_eq_pairing
end AspisR1S9RawIdentityRowV1
end
