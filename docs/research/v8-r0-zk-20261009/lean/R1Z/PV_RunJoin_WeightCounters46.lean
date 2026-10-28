import R1Z.PV_B2_D_SmallScalar
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCounters46
open Aeneas Aeneas.Std

theorem add0 : Usize.wrapping_add 0#usize 1#usize=1#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add0

theorem add1 : Usize.wrapping_add 1#usize 1#usize=2#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add1

theorem add2 : Usize.wrapping_add 2#usize 1#usize=3#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add2

theorem add3 : Usize.wrapping_add 3#usize 1#usize=4#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add3

theorem shift0 : UScalar.cast .U32 (Usize.wrapping_mul 2#usize 0#usize)=0#u32 := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms shift0

theorem shift1 : UScalar.cast .U32 (Usize.wrapping_mul 2#usize 1#usize)=2#u32 := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms shift1

theorem shift2 : UScalar.cast .U32 (Usize.wrapping_mul 2#usize 2#usize)=4#u32 := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms shift2

theorem shift3 : UScalar.cast .U32 (Usize.wrapping_mul 2#usize 3#usize)=6#u32 := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms shift3

theorem shift4 : UScalar.cast .U32 (Usize.wrapping_mul 2#usize 4#usize)=8#u32 := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms shift4
end R1Z.PV_RunJoin_WeightCounters46
