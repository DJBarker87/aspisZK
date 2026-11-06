import NJA_CountStep

set_option autoImplicit false
namespace NJE_CountArithmetic
open Aeneas Aeneas.Std Result

theorem sub_value (a b : Usize) (order : b.val≤a.val) :
    (Usize.wrapping_sub a b).val=a.val-b.val := by
 rw [Usize.wrapping_sub_val_eq]
 have ha := a.hSize
 have hb := b.hSize
 have eq : a.val+(UScalar.size .Usize-b.val)=(a.val-b.val)+UScalar.size .Usize := by omega
 rw [eq,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
 exact Nat.mod_eq_of_lt (by omega)

theorem add_value (a b : Usize) (small : a.val+b.val<UScalar.size .Usize) :
    (Usize.wrapping_add a b).val=a.val+b.val := by
 rw [Usize.wrapping_add_val_eq]
 exact Nat.mod_eq_of_lt small

theorem deficit (i q : Usize) (lower : i.val≤q.val) (upper : q.val ≤ i.val + 2) :
    (Usize.wrapping_sub 2#usize (Usize.wrapping_sub q i)).val=2-(q.val-i.val) := by
 have difference := sub_value q i lower
 rw [sub_value 2#usize (Usize.wrapping_sub q i) (by scalar_tac),difference]
 rfl

theorem count_value (c i q : Usize) (count_bound : c.val≤576)
    (lower : i.val≤q.val) (upper : q.val ≤ i.val + 2) :
    (Usize.wrapping_add c (Usize.wrapping_sub 2#usize (Usize.wrapping_sub q i))).val=
      c.val+(2-(q.val-i.val)) := by
 rw [add_value]
 · rw [deficit i q lower upper]
 · rw [deficit i q lower upper]
   have size := (1024#usize).hSize
   change 1024<UScalar.size .Usize at size
   omega

theorem update_result {α : Type} (a : Array α 16#usize) (w : Usize) (x : α)
    (bound : w.val<16) : Array.update a w x=ok (a.set w x) := by
 unfold Array.update
 have hw : w.val<a.val.length := by have h : a.val.length=16 := a.property;omega
 change (match a.val[w.val]? with
   | none => Result.fail Error.arrayOutOfBounds
   | some _ => Result.ok ⟨a.val.set w.val x,_⟩)=ok (a.set w x)
 rw [List.getElem?_eq_getElem hw]
 rfl

#print sub_value
#print axioms sub_value
#print add_value
#print axioms add_value
#print deficit
#print axioms deficit
#print count_value
#print axioms count_value
#print update_result
#print axioms update_result
end NJE_CountArithmetic
