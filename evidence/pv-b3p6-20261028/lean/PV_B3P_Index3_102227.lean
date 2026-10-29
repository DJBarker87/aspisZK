import PV_B3P_ArrayWrite227
import PV_B3P_LiftHeadEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def get3_2 {α : Type} (xs : Array α 3#usize) : α :=
  xs.val[2]'(by have h:=xs.property; change xs.val.length=3 at h; omega)

theorem index3_2 {α : Type} (xs : Array α 3#usize) :
    Array.index_usize xs 2#usize = .ok (get3_2 xs) :=
  PV_B3P_SelectIndex227.index_value xs 2#usize (by change 2<3; omega)

theorem borrow3_2 {α : Type} (xs : Array α 3#usize) :
    Array.index_mut_usize xs 2#usize = .ok (get3_2 xs,Aeneas.Std.Array.set xs 2#usize) :=
  PV_B3P_ArrayWrite227.borrow xs 2#usize (by change 2<3; omega)

theorem update3_2 {α : Type} (xs : Array α 3#usize) (value : α) :
    Array.update xs 2#usize value = .ok (Aeneas.Std.Array.set xs 2#usize value) :=
  PV_B3P_ArrayWrite227.update xs 2#usize (by change 2<3; omega) value
#print axioms index3_2
#print axioms borrow3_2
#print axioms update3_2
end PV_B3P_Binding10227
