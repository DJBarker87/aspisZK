import PV_B3P_ArrayWrite227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def get3_1 {α : Type} (xs : Array α 3#usize) : α :=
  xs.val[1]'(by have h:=xs.property; change xs.val.length=3 at h; omega)

theorem index3_1 {α : Type} (xs : Array α 3#usize) :
    Array.index_usize xs 1#usize = .ok (get3_1 xs) :=
  PV_B3P_SelectIndex227.index_value xs 1#usize (by change 1<3; omega)

theorem borrow3_1 {α : Type} (xs : Array α 3#usize) :
    Array.index_mut_usize xs 1#usize = .ok (get3_1 xs,Array.set xs 1#usize) :=
  PV_B3P_ArrayWrite227.borrow xs 1#usize (by change 1<3; omega)

theorem update3_1 {α : Type} (xs : Array α 3#usize) (value : α) :
    Array.update xs 1#usize value = .ok (Array.set xs 1#usize value) :=
  PV_B3P_ArrayWrite227.update xs 1#usize (by change 1<3; omega)
#print axioms index3_1
#print axioms borrow3_1
#print axioms update3_1
end PV_B3P_Binding10227
