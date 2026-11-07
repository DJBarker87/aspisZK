import PCF_ChildLaws
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_EncodePrefix
open AspisR1.S2K

theorem before (xs : List U32) (k : Nat) (out : Array U8 32#usize) (j : Nat)
    (prior : j < 4*k) : (DigestBytes.fold xs k out).val[j]! = out.val[j]! := by
  induction xs generalizing k out with
  | nil => rfl
  | cons x xs ih =>
    simp only [DigestBytes.fold]
    rw [ih (k+1) _ (by omega)]
    exact List.getElem!_setSlice!_prefix _ _ _ _ prior

theorem head_zero (a : U32) (xs : List U32) (out : Array U8 32#usize) :
    (DigestBytes.fold (a::xs) 0 out).val[0]! =
      (core.num.U32.to_le_bytes a).val[0]! := by
  change (DigestBytes.fold xs 1 (out.setSlice! 0 (core.num.U32.to_le_bytes a).val)).val[0]! = _
  rw [before xs 1 _ 0 (by decide)]
  apply List.getElem!_setSlice!_middle
  have hw := (core.num.U32.to_le_bytes a).property
  have ho := out.property
  scalar_tac

#print axioms before
#print axioms head_zero
end PCF_EncodePrefix
