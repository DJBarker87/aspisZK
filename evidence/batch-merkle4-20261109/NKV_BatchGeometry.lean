import NKV_ConcreteChildren
set_option autoImplicit false
namespace NKV_BatchGeometry
open Aeneas Aeneas.Std Result

theorem span0 : Usize.wrapping_sub 10#usize 0#usize=10#usize := by
 apply UScalar.eq_of_val_eq
 have x : (10#usize).val=10 := by scalar_tac
 have y : (0#usize).val=0 := by scalar_tac
 have cap : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 rw [Usize.wrapping_sub_val_eq,x,y,Nat.sub_zero,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem span1 : Usize.wrapping_sub 22#usize 10#usize=12#usize := by
 apply UScalar.eq_of_val_eq
 have x : (22#usize).val=22 := by scalar_tac
 have y : (10#usize).val=10 := by scalar_tac
 have z : (12#usize).val=12 := by scalar_tac
 have cap : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 rw [Usize.wrapping_sub_val_eq,x,y,z,
   show 22+(UScalar.size .Usize-10)=12+UScalar.size .Usize by omega,
   Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem slot (batch tree : Usize) (b : batch.val<2) (t : tree.val<3) :
 (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) tree).val=3*batch.val+tree.val ∧
 (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) tree).val<6 := by
 have three : (3#usize).val=3 := by scalar_tac
 have mul := AspisR1.Port3_Wrapping.wrap_mul_value 3#usize batch (by rw [three];omega)
 have add := AspisR1.Port3_Wrapping.wrap_add_value (Usize.wrapping_mul 3#usize batch) tree
   (by rw [mul,three];omega)
 rw [add,mul,three]
 exact ⟨rfl,by omega⟩

#print axioms span0
#print axioms span1
#print axioms slot
end NKV_BatchGeometry
