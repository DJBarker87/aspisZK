import PV_B3_ZeroLinears
namespace PV_B3_ZeroMask117
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_B3_ZeroArithmetic
set_option autoImplicit false

theorem tower0 : host_arithmetic.mul_tower_basis Z 0#usize = ok Z := by with_unfolding_all rfl
theorem tower1 : host_arithmetic.mul_tower_basis Z 1#usize = ok Z := by with_unfolding_all rfl
theorem tower2 : host_arithmetic.mul_tower_basis Z 2#usize = ok Z := by with_unfolding_all rfl
theorem tower3 : host_arithmetic.mul_tower_basis Z 3#usize = ok Z := by with_unfolding_all rfl

theorem factor0 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 0#usize = ok 0#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor0
theorem factor1 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 1#usize = ok 2#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor1
theorem factor2 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 2#usize = ok 4#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor2
theorem factor3 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 3#usize = ok 6#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor3
theorem factor4 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 4#usize = ok 8#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor4
theorem factor5 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 5#usize = ok 10#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor5
theorem factor6 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 6#usize = ok 12#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor6
theorem factor7 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 7#usize = ok 14#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor7
theorem factor8 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 8#usize = ok 16#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor8
theorem factor9 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 9#usize = ok 18#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor9
theorem factor10 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 10#usize = ok 20#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor10
theorem factor11 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 11#usize = ok 22#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor11
theorem factor12 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 12#usize = ok 24#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor12
theorem factor13 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 13#usize = ok 26#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor13
theorem factor14 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 14#usize = ok 13#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor14
theorem factor15 : Array.index_usize host_arithmetic.FACTOR_EXPONENTS 15#usize = ok 25#u8 := by
  unfold host_arithmetic.FACTOR_EXPONENTS
  rfl
#print axioms factor15
theorem maskfactor0 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 0#usize = ok 1#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor0
theorem maskfactor1 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 1#usize = ok 3#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor1
theorem maskfactor2 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 2#usize = ok 5#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor2
theorem maskfactor3 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 3#usize = ok 7#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor3
theorem maskfactor4 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 4#usize = ok 9#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor4
theorem maskfactor5 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 5#usize = ok 11#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor5
theorem maskfactor6 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 6#usize = ok 15#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor6
theorem maskfactor7 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 7#usize = ok 17#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor7
theorem maskfactor8 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 8#usize = ok 19#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor8
theorem maskfactor9 : Array.index_usize host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS 9#usize = ok 21#u8 := by
  unfold host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
  rfl
#print axioms maskfactor9
theorem selected : host_arithmetic.selected_coefficients (Array.repeat 16#usize Z) =
    ok (Array.repeat 27#usize Z) := by
  simp (disch := decide) only [host_arithmetic.selected_coefficients,
    factor0,factor1,factor2,factor3,factor4,factor5,factor6,factor7,factor8,factor9,factor10,factor11,factor12,factor13,factor14,factor15,lift,index_repeat,update_repeat,tower0,tower1,tower2,tower3,bind_tc_ok]

theorem mask : host_arithmetic.mask_only_coefficients (Array.repeat 27#usize Z)
    (Array.repeat 10#usize Z) = ok (Array.repeat 27#usize Z) := by
  simp (disch := decide) only [host_arithmetic.mask_only_coefficients,
    maskfactor0,maskfactor1,maskfactor2,maskfactor3,maskfactor4,maskfactor5,maskfactor6,maskfactor7,maskfactor8,maskfactor9,lift,index_repeat,update_repeat,tower0,tower1,tower2,tower3,bind_tc_ok]

theorem horner : host_arithmetic.selected_horner (Array.repeat 27#usize Z) Z = ok Z := by
  simp (disch := decide) only [host_arithmetic.selected_horner,aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE,prepare,
    index_repeat,prepared_mul,PV_B3_ZeroArithmetic.add,bind_tc_ok]

theorem power : host_arithmetic.mask_power_26 Z = ok Z := by
  simp only [host_arithmetic.mask_power_26,square,mul,bind_tc_ok]

theorem source : host_arithmetic.state_only_selected_mask_value
    (Array.repeat 16#usize Z) (Array.repeat 10#usize Z) Z (Array.repeat 10#usize Z) = ok Z := by
  simp only [host_arithmetic.state_only_selected_mask_value,PV_B3_ZeroLinears.source,
    selected,mask,horner,power,one_add,one_mul,PV_B3_ZeroArithmetic.add,bind_tc_ok]

#print axioms tower0
#print axioms tower1
#print axioms tower2
#print axioms tower3
#print axioms selected
#print axioms mask
#print axioms horner
#print axioms power
#print axioms source
end PV_B3_ZeroMask117
