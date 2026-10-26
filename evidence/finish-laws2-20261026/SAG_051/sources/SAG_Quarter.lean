import SAG_QuarterBase
import SAG_QuarterLift
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_Quarter
open Aeneas Aeneas.Std

theorem source_scalar : SAG_UnrestrictedScale.wideScalarEmbedding 536870912#u32 =
    (RoundPairing.quarter : AspisWideTower.WideExact) := by
  rw [SAG_UnrestrictedScale.wideScalarEmbedding_eq_algebraMap]
  apply SAG_QuarterLift.value
  change (4 : ZMod 2147483647) * 536870912 = 1
  exact SAG_QuarterBase.four_times

#print axioms source_scalar
end AspisR1.SAG_Quarter
end
