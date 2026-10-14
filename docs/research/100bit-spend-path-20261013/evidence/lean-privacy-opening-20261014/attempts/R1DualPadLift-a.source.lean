import R1DualPadWord
import R1DualPadQuadratic

/-! The existing quadratic two-pad identity lifts to whole words. Raw
observation preimages and membership in the common balanced pad space are
explicit inputs. No rank, source correspondence, or transcript-law premise
is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DualPadLift

open DualPadWord
open scoped BigOperators

variable {K : Type} [Field K] {nu : K}
  [Fact (∀ r : K, r ^ 2 ≠ nu + 0 * r)]
  {C I O : Type} [Fintype C] [AddCommGroup O] [Module K O]

abbrev E (K : Type) [Field K] (nu : K) := DualPadQuadratic.Ext K nu

def uCoeff (gamma : E K nu) (lane : C → Nat) (c : C) : K :=
  DualPad.u (gamma ^ 27).re (gamma ^ 27).im (gamma ^ 28).re (gamma ^ 28).im
    (gamma ^ lane c).re (gamma ^ lane c).im

def vCoeff (gamma : E K nu) (lane : C → Nat) (c : C) : K :=
  DualPad.v (gamma ^ 27).re (gamma ^ 27).im (gamma ^ 28).re (gamma ^ 28).im
    (gamma ^ lane c).re (gamma ^ lane c).im

def batch (gamma : E K nu) (lane : C → Nat) (words : C → I → K) : I → E K nu :=
  fun i => ∑ c, gamma ^ lane c * algebraMap K (E K nu) (words c i)

theorem coefficients_cancel (gamma : E K nu) (hgamma : gamma.im ≠ 0)
    (lane : C → Nat) (c : C) :
    gamma ^ lane c + gamma ^ 27 * algebraMap K (E K nu) (uCoeff gamma lane c) +
      gamma ^ 28 * algebraMap K (E K nu) (vCoeff gamma lane c) = 0 :=
  DualPadQuadratic.pad_correction gamma hgamma (lane c)

/-- Two legal balanced pad corrections preserve all raw pad observations
and reproduce the entire extension-field batch of the original words. -/
theorem correction (gamma : E K nu) (hgamma : gamma.im ≠ 0)
    (lane : C → Nat) (B : Submodule K (I → K))
    (raw : (I → K) →ₗ[K] O) (delta noise : C → I → K)
    (hdelta : ∀ c, delta c ∈ B) (hnoise : ∀ c, noise c ∈ B)
    (hraw : ∀ c, raw (noise c) = raw (delta c)) :
    repair (uCoeff gamma lane) delta noise ∈ B ∧
    repair (vCoeff gamma lane) delta noise ∈ B ∧
    raw (repair (uCoeff gamma lane) delta noise) = 0 ∧
    raw (repair (vCoeff gamma lane) delta noise) = 0 ∧
    batch gamma lane noise +
        gamma ^ 27 • embed (repair (uCoeff gamma lane) delta noise) +
        gamma ^ 28 • embed (repair (vCoeff gamma lane) delta noise) =
      batch gamma lane delta := by
  refine ⟨repair_mem B _ delta noise hdelta hnoise,
    repair_mem B _ delta noise hdelta hnoise,
    repair_raw_zero raw _ delta noise hraw,
    repair_raw_zero raw _ delta noise hraw, ?_⟩
  exact full_word_eq (fun c => gamma ^ lane c) (gamma ^ 27) (gamma ^ 28)
    (uCoeff gamma lane) (vCoeff gamma lane) delta noise
    (coefficients_cancel gamma hgamma lane)

/-- Whole-word equality preserves any fixed deterministic observation,
including compositions of folds. This does not identify a Rust payload. -/
theorem observations_eq {V : Type} (gamma : E K nu) (hgamma : gamma.im ≠ 0)
    (lane : C → Nat) (delta noise : C → I → K)
    (observe : (I → E K nu) → V) :
    observe (batch gamma lane noise +
        gamma ^ 27 • embed (repair (uCoeff gamma lane) delta noise) +
        gamma ^ 28 • embed (repair (vCoeff gamma lane) delta noise)) =
      observe (batch gamma lane delta) := by
  apply congrArg observe
  exact full_word_eq (fun c => gamma ^ lane c) (gamma ^ 27) (gamma ^ 28)
    (uCoeff gamma lane) (vCoeff gamma lane) delta noise
    (coefficients_cancel gamma hgamma lane)

#print axioms coefficients_cancel
#print axioms correction
#print axioms observations_eq

end AspisR1.DualPadLift
end
