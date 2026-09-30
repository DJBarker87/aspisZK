import AspisV8R19.AdaptiveFirstReadLoss

/-! Indicator form of the one-step uniform-state collision bound.

This is still a one-step statement for a fixed prior read list.  It does not
assert source-state uniformity or perform the whole-run union bound. -/
set_option autoImplicit false
namespace AspisV8R19.UniformStateFirstHitMean

open DuplexFrames SourceDuplexStep
open OracleResampling UniformStateFirstHit
noncomputable section

noncomputable def badIndicator (reads : List Bytes) (s : State) : ℚ := by
  classical
  exact if BadState reads (bytes s) then 1 else 0

theorem mean_indicator_card {S : Type} [Fintype S]
    (p : S → Prop) [DecidablePred p] :
    mean (fun s : S => if p s then 1 else 0) =
      ((Finset.univ.filter p).card : ℚ) / Fintype.card S := by
  unfold mean
  congr 1
  simpa using
    (Finset.sum_boole (R := ℚ) p (Finset.univ : Finset S))

theorem mean_bad_indicator_eq_fraction (reads : List Bytes) :
    mean (badIndicator reads) =
      uniformBadFraction reads := by
  classical
  unfold badIndicator uniformBadFraction badStates
  exact mean_indicator_card (fun s : State => BadState reads (bytes s))

theorem mean_bad_indicator_bound (reads : List Bytes) :
    mean (badIndicator reads) ≤
      (reads.length : ℚ) / (256 ^ 32 : ℚ) := by
  rw [mean_bad_indicator_eq_fraction]
  exact uniform_bad_bound reads

#print axioms mean_bad_indicator_eq_fraction
#print axioms mean_bad_indicator_bound

end
end AspisV8R19.UniformStateFirstHitMean
