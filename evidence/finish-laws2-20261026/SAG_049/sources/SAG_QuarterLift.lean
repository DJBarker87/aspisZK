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
  unfold RoundPairing.quarter
  have four_times : (4 : Model) * algebraMap Base Model q = 1 := by
    have lifted := congrArg (algebraMap Base Model) base
    simpa only [map_mul,map_ofNat,map_one] using lifted
  have nz : (4 : Model) ≠ 0 := by
    intro h
    rw [h,zero_mul] at four_times
    exact zero_ne_one four_times
  calc
    algebraMap Base Model q = (4 : Model)⁻¹ * ((4 : Model) * algebraMap Base Model q) := by
      rw [←mul_assoc,inv_mul_cancel₀ nz,one_mul]
    _ = (4 : Model)⁻¹ := by rw [four_times,mul_one]

#print axioms value
end AspisR1.SAG_QuarterLift
end
