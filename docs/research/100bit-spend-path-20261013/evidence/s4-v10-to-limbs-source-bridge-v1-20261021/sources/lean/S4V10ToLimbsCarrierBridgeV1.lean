import Aeneas
import AspisR1FastDotsCurrent.ToLimbsBody
import AspisR1EbyKPushWideToQ
import S4V10CarrierMapV1
open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace S4V10ToLimbsCarrierBridgeV1

abbrev V10Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev AcceptedV10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev CurrentWide := AspisR1EbyKPushWideToQ.Wide

def wideToAccepted (x : V10Wide) : AcceptedV10Wide :=
  { c0 :=
      { c0 := { a := x.c0.c0.a, b := x.c0.c0.b }
        c1 := { a := x.c0.c1.a, b := x.c0.c1.b } }
    c1 :=
      { c0 := { a := x.c1.c0.a, b := x.c1.c0.b }
        c1 := { a := x.c1.c1.a, b := x.c1.c1.b } } }

def wideToCurrent (x : V10Wide) : CurrentWide :=
  { c0 :=
      { c0 := { a := x.c0.c0.a, b := x.c0.c0.b }
        c1 := { a := x.c0.c1.a, b := x.c0.c1.b } }
    c1 :=
      { c0 := { a := x.c1.c0.a, b := x.c1.c0.b }
        c1 := { a := x.c1.c1.a, b := x.c1.c1.b } } }

theorem wideToCurrent_eq_acceptedMap (x : V10Wide) :
    wideToCurrent x =
      AspisR1FastDotsV10CarrierMapV1.wideToEbyK (wideToAccepted x) := by
  rfl

theorem v10_to_limbs_eq_current
    (x : V10Wide) :
    AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact.to_limbs x =
      AspisR1EbyKPushWideToQ.toLimbs (wideToCurrent x) := by
  rfl

theorem v10_to_limbs_eq_acceptedMap (x : V10Wide) :
    AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact.to_limbs x =
      AspisR1EbyKPushWideToQ.toLimbs
        (AspisR1FastDotsV10CarrierMapV1.wideToEbyK (wideToAccepted x)) := by
  rw [← wideToCurrent_eq_acceptedMap]
  exact v10_to_limbs_eq_current x

#print axioms v10_to_limbs_eq_current
#print axioms v10_to_limbs_eq_acceptedMap
#print axioms wideToCurrent_eq_acceptedMap

end S4V10ToLimbsCarrierBridgeV1
