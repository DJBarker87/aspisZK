import NNG_LegacyEquality136
set_option autoImplicit false
namespace AspisR1.NNG_LegacyNe136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport

theorem ne (x y : aspis_core.field.QM31) :
 core.cmp.PartialEq.ne.trait_default AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
   (toT1 x) (toT1 y)=.ok (decide (x≠y)) := by
 change (do let b←AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq (toT1 x) (toT1 y)
            ok (decide (¬b=true)))=_
 rw [NNG_LegacyEquality136.qm,bind_tc_ok]
 by_cases h : x=y <;> simp [h]
#print axioms ne
end AspisR1.NNG_LegacyNe136
