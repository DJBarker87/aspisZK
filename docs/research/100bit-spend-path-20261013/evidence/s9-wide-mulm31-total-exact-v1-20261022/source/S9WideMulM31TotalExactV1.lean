import S9WideMulM31UpperResultMapV1
import S3PowersLowTotalV1
import CurrentWideMulM31V13

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31TotalExactV1
open AspisR1S9WideMulM31FullResultMapV1

/-- Invert only a successful mapped Result; failures and divergence are
preserved by mapR and therefore cannot map to `.ok`. -/
theorem mapR_ok_inv {A B : Type} (f : A → B) (r : Result A) (y : B)
    (h : mapR f r = .ok y) :
    ∃ x, r = .ok x ∧ f x = y := by
  cases r with
  | ok x => exact ⟨x, rfl, Result.ok.inj h⟩
  | fail e => simp [mapR] at h
  | div => simp [mapR] at h

/-- Current-field totality constructs a successful output for the actual
attempt16 extracted call via the full-Result mapper. On canonical mapped input,
the same returned value has the retained current-field decode meaning. -/
theorem actual_wide_mul_m31_total_exact
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact)
    (s : AspisR1S9WideMulM31CutV1.field.M31)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (mapWide x)) :
    ∃ z, AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31 x s = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide (mapWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide (mapWide z) =
        AspisR1CurrentWide.Proof.decodeWide (mapWide x) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding s := by
  obtain ⟨y, hy⟩ := AspisR1S3PowersLowTotalV1.wide_mul_m31_total (mapWide x) s
  have hsame : mapR mapWide
      (AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31 x s) = .ok y := by
    rw [AspisR1S9WideMulM31UpperResultMapV1.wide_mul_m31_result_map]
    exact hy
  obtain ⟨z, hz, hzy⟩ := mapR_ok_inv mapWide _ y hsame
  have hmeaning := AspisR1CurrentWide.Proof.wide_mul_m31_success
    (mapWide x) y s hx hy
  refine ⟨z, hz, ?_, ?_⟩
  · rw [hzy]
    exact hmeaning.1
  · rw [hzy]
    exact hmeaning.2

#print axioms mapR_ok_inv
#print axioms actual_wide_mul_m31_total_exact

end AspisR1S9WideMulM31TotalExactV1
