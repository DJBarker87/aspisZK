import NJE_CountArithmetic
import NJA_CountDrop
import MultiproofConeLiveOrder

set_option autoImplicit false
namespace NJE_CountArrayFrame
open Aeneas Aeneas.Std

theorem get_set {α : Type} [Inhabited α] (a : Array α 16#usize) (w : Usize) (x : α)
    (bound : w.val<16) (j : Nat) (hj : j<16) :
    (a.set w x).val[j]! = (if j=w.val then x else a.val[j]!) := by
 have len : a.val.length=16 := a.property
 by_cases same : j=w.val
 · subst j
   simp [Array.set_val_eq,List.getElem!_eq_getElem?_getD,
     List.getElem?_set_self (by omega : w.val<a.val.length)]
 · simp [Array.set_val_eq,List.getElem!_eq_getElem?_getD,
     List.getElem?_set_ne (Ne.symm same),same]

theorem keys_write (a : Array U32 16#usize) (i w : Usize)
    (ib : i.val<16) (wb : w.val<16) (j : Nat) (jb : j<16) :
    NJA_CountDrop.keys (a.set w (U32.wrapping_shr (a.val[i.val]!) 1#u32)) j=
      AspisR1.MultiproofConeLiveOrder.write (NJA_CountDrop.keys a) i.val w.val j := by
 unfold NJA_CountDrop.keys
 rw [get_set a w _ wb j jb]
 unfold AspisR1.MultiproofConeLiveOrder.write
 split <;> simp_all only [NJA_CountStep.shift_one]

#print get_set
#print axioms get_set
#print keys_write
#print axioms keys_write
end NJE_CountArrayFrame
