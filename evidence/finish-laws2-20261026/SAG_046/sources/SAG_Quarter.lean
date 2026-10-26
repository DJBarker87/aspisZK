import SAG_UnrestrictedScale
import SAG_QuarterBase
import SAG_QuarterTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_Quarter
open Aeneas Aeneas.Std
abbrev Model := AspisWideTower.WideExact

theorem source_scalar : SAG_UnrestrictedScale.wideScalarEmbedding 536870912#u32 =
    RoundPairing.quarter := by
  rw [SAG_UnrestrictedScale.wideScalarEmbedding_eq_algebraMap]
  have decoded : R17CurrentM31Semantics.decode 536870912#u32 =
      (536870912 : ZMod 2147483647) := rfl
  rw [decoded]
  exact SAG_QuarterTransport.value (algebraMap (ZMod 2147483647) Model)
    (536870912 : ZMod 2147483647) SAG_QuarterBase.four_times

#print axioms source_scalar
end AspisR1.SAG_Quarter
end
