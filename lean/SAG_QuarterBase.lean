import R1RoundPairing
set_option autoImplicit false
namespace AspisR1.SAG_QuarterBase
abbrev Base := ZMod 2147483647

theorem four_times : (4 : Base) * 536870912 = 1 := by
  apply ZMod.val_injective 2147483647
  change (4 * 536870912) % 2147483647 = 1
  norm_num

#print axioms four_times
end AspisR1.SAG_QuarterBase
