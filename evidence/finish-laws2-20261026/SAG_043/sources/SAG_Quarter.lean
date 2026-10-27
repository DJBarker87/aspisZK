import SAG_UnrestrictedScale
import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_Quarter
abbrev Model := AspisWideTower.WideExact

theorem four_times : (4 : Model) * 536870912 = 1 := by
  have base : (4 : ZMod 2147483647) * 536870912 = 1 := by norm_num
  have lifted := congrArg (algebraMap (ZMod 2147483647) Model) base
  simpa only [map_mul,map_natCast,map_one] using lifted

theorem value : (536870912 : Model) = RoundPairing.quarter := by
  have nz : (4 : Model) ≠ 0 := by
    intro h
    have bad := four_times
    rw [h,zero_mul] at bad
    exact zero_ne_one bad
  change (536870912 : Model) = (4 : Model)⁻¹
  calc
    (536870912 : Model) = (4 : Model)⁻¹ * ((4 : Model) * 536870912) := by
      rw [←mul_assoc,inv_mul_cancel₀ nz,one_mul]
    _ = (4 : Model)⁻¹ := by rw [four_times,mul_one]

theorem source_scalar : SAG_UnrestrictedScale.wideScalarEmbedding (536870912 : Aeneas.Std.U32) =
    RoundPairing.quarter := by
  rw [SAG_UnrestrictedScale.wideScalarEmbedding_eq_algebraMap]
  change algebraMap (ZMod 2147483647) Model (536870912 : ZMod 2147483647) = _
  rw [map_natCast]
  exact value

#print axioms four_times
#print axioms value
#print axioms source_scalar
end AspisR1.SAG_Quarter
end
