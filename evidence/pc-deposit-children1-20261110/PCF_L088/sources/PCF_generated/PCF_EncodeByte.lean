import PCF_EncodePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_EncodeByte
open AspisR1.S2K

theorem at_word (xs : List U32) (k : Nat) (out : Array U8 32#usize)
    (n j : Nat) (word : n < xs.length) (byte : j < 4)
    (fits : 4*(k+n)+j < 32) :
    (DigestBytes.fold xs k out).val[4*(k+n)+j]! =
      (core.num.U32.to_le_bytes xs[n]).val[j]! := by
  induction n generalizing xs k out with
  | zero =>
    cases xs with
    | nil => simp at word
    | cons x xs =>
      simp only [Nat.add_zero,List.getElem_cons_zero]
      change (DigestBytes.fold xs (k+1) (out.setSlice! (4*k) (core.num.U32.to_le_bytes x).val)).val[4*k+j]! = _
      rw [PCF_EncodePrefix.before xs (k+1) _ _ (by omega)]
      have hw := (core.num.U32.to_le_bytes x).property
      have ho := out.property
      have hmiddle := List.getElem!_setSlice!_middle out.val
        (core.num.U32.to_le_bytes x).val (4*k) (4*k+j) (by scalar_tac)
      change (out.val.setSlice! (4*k) (core.num.U32.to_le_bytes x).val)[4*k+j]! = _
      simpa only [Nat.add_sub_cancel_left] using hmiddle
  | succ n ih =>
    cases xs with
    | nil => simp at word
    | cons x xs =>
      simp only [List.getElem_cons_succ,DigestBytes.fold]
      have eq : 4*(k+(n+1))+j = 4*((k+1)+n)+j := by omega
      rw [eq]
      apply ih
      omega
#print axioms at_word
end PCF_EncodeByte
