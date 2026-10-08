import R0P.SemD2
import R0C.V3.DuplexQ
import R0C.CircleRows
import R0P.SemD3Glue

/-!
G16 interface finding. `Duplex.Params` leaves `σ : Nat → State → Cv`
generic, so a mixed challenge type can map semantic rounds through
`R0P.SemSource.semChal`; the existing five-round Q22 parameter is not that protocol.
More fundamentally, the fixed `FS2.D2` premise only supplies a doomed
prefix. The semantic density bound for an α-round separately requires
`semRoundDegreeChecked`. The theorem below witnesses that this condition is
not derivable from the type of an arbitrary prefix: a transcript's current
round polynomial may be `X^28`.
-/

set_option autoImplicit false

namespace R0P.SemSource
open Polynomial Sumcheck

theorem degree_check_not_automatic {K : Type} [Field K]
    (pref : Fin 14 → K) :
    ¬ R0P.semRoundDegreeChecked
      (fixedStrat (fun _ : Fin 10 => (X : K[X]) ^ 28))
      ⟨14, by decide⟩ pref := by
  intro h
  have h' := h
  unfold R0P.semRoundDegreeChecked at h'
  simp only [dif_pos (show 14 ≤ (⟨14, by decide⟩ : Fin 24).val from Nat.le_refl 14)] at h'
  change ((X : K[X]) ^ 28).natDegree ≤ 27 at h'
  have hn : 28 ≤ 27 := by
    simpa only [Polynomial.natDegree_X_pow] using h'
  omega

#print axioms degree_check_not_automatic

end R0P.SemSource
