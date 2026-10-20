import ClaimDotConcreteAdapterV1
import FinishDotSourceABI

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5ClaimScalarFinishCanonical

open AspisR1S5ClaimDotConcreteAdapter
open AspisR1CurrentPreparedClaim

abbrev PushState := AspisR1FinishDotSourceABI.PushState
abbrev ClaimWide := aspis_core.field.WideExact

theorem concrete_finishDot_success_canonical
    (s : PushState) (rawFn : AspisR1EbyKPushDotBackend.RawFn) (out : ClaimWide)
    (h : (concreteOps rawFn).finishDot s = .ok out) : Concrete.Canonical out := by
  unfold concreteOps at h
  cases hr : AspisR1FinishDotSourceABI.finishFromPush s with
  | fail e => simp [hr] at h
  | div => simp [hr] at h
  | ok finish =>
      simp [hr] at h
      subst out
      exact ClaimParser.canonical_from_finish finish
        (AspisR1FinishDotSourceABI.finishFromPush_success_canonical s finish hr).1

#print axioms concrete_finishDot_success_canonical

end AspisR1S5ClaimScalarFinishCanonical
