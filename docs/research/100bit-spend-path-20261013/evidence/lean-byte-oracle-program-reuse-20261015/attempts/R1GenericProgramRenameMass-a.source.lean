import AspisV8R19.OracleProgramOps
import AspisV8R19.AdaptiveFirstReadLaw

/-! A program's independent-answer mass is invariant under renaming its
addresses, provided the observation is mapped along with the trace. This is
only an independent-answer statement; memoized/shared-oracle transport still
needs the injectivity premise of `lazy_rename`. -/
set_option autoImplicit false
namespace AspisR1.GenericProgramRenameMass

open AspisV8PairedCommitment AspisV8R19.OracleResampling
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

variable {I J A O : Type}

theorem independentMean_rename [Fintype A]
    (label : I → J) (p : Program I A O) (observe : View J A O → ℚ) :
    independentMean (rename label p) observe =
      independentMean p (fun v => observe (mapView label v)) := by
  induction p generalizing observe with
  | done o => rfl
  | ask i next ih =>
      simp only [rename, independentMean]
      apply mean_congr
      intro a
      simpa [mapView] using
        ih a (fun v => observe ((label i, a) :: v.1, v.2))

#print axioms independentMean_rename

end AspisR1.GenericProgramRenameMass
