import AspisV8R17.SourceOpeningResidual
import AspisV8R16.TransportDual
import Mathlib.Algebra.BigOperators.Fin

/-! Compose the arbitrary-coefficient transport, source chord transpose,
and channel-specific residual updates. The original weight vector is still
an explicit input; no claim about its Rust materialization is hidden here. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

def extendFin1024 (w : Fin 1024 → F) (i : ℕ) : F :=
  if hi : i<1024 then w ⟨i,hi⟩ else 0

theorem rangeDot_extendFin1024 (w : Fin 1024 → F) (q : ℕ → F) :
    rangeDot 1024 (extendFin1024 w) q = ∑ i : Fin 1024, w i*q i.val := by
  unfold rangeDot
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [extendFin1024, i.isLt]

theorem transported_source_opening_pairing (half : F)
    (inactive : Finset (Fin 1024)) (pivot : Fin 1024) (order : Fin 1024 ≃ Fin 1024)
    (w : Fin 1024 → F) (q : ℕ → F) (a b c tau : F) (structured : Bool) :
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual inactive pivot order w)) a b c tau structured) q =
      (∑ r : Fin 1024, w r * AspisV8R16.inverseTransport inactive pivot order
        (fun j => sourceChord half q a b c j.val) r) +
      (if structured then tau^3 else tau)*q 1023 +
      (if structured then tau^4 else tau^2)*(b*q 1022-c*q 1021) := by
  rw [source_quotient_weights_pairing, rangeDot_extendFin1024,
    ← AspisV8R16.inverseTransport_dot]

#print axioms rangeDot_extendFin1024
#print axioms transported_source_opening_pairing
end AspisV8R17
