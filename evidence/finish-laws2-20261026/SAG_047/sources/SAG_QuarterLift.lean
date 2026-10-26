import SAG_UnrestrictedScale
import SAG_QuarterTransport
import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_QuarterLift
abbrev Base := SAG_UnrestrictedScale.MExact
abbrev Model := AspisWideTower.WideExact

theorem value (q : Base) (base : (4 : Base) * q = 1) :
    algebraMap Base Model q = (RoundPairing.quarter : Model) := by
  change algebraMap Base Model q = (4 : Model)⁻¹
  exact SAG_QuarterTransport.value (algebraMap Base Model) q base

#print axioms value
end AspisR1.SAG_QuarterLift
end
