import S4V10ToLimbsCarrierBridgeV1
import S4CurrentHeadTermForwardRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsV10InstalledToLimbsSlotV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := S4V10ToLimbsCarrierBridgeV1.V10Wide

/-- The generated V10 method body is the exact conversion installed into the
head operation record, after the explicit V10-to-EbyK carrier map. -/
theorem literal_to_limbs_installed (base : Ops) (x : Wide) :
    AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact.to_limbs x =
      (AspisR1FastDotsCurrentHeadTermForwardRootV1.install base).wideToLimbs
        (S4V10ToLimbsCarrierBridgeV1.wideToCurrent x) := by
  change AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact.to_limbs x =
    AspisR1EbyKPushWideToQ.toLimbs (S4V10ToLimbsCarrierBridgeV1.wideToCurrent x)
  exact S4V10ToLimbsCarrierBridgeV1.v10_to_limbs_eq_current x

#print axioms literal_to_limbs_installed

end AspisR1FastDotsV10InstalledToLimbsSlotV1
