import PCI_ValidateRef.Funs
import PCF_ArrayIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidatePrefix
theorem ok_ite {T : Type} (p : Prop) [Decidable p] (a b : T) :
    (ok (if p then a else b) : Result T) = if p then ok a else ok b := by
  by_cases h : p <;> simp only [h,ite_true,ite_false]

/-- Pure NCO prefix over arbitrary logged product replies. Same rejection order. -/
def code (first second : Bool) (occupied inverse sentinel : U32)
    (products : Array U32 3#usize) (scan : Bool) : U8 :=
  if first then
    if second then
      if occupied >= 2147483647#u32 then 2#u8
      else if inverse >= 2147483647#u32 then 3#u8
      else if products.val[0]! != 0#u32 then 4#u8
      else if products.val[1]! != occupied then 5#u8
      else if products.val[2]! != 0#u32 then 6#u8
      else if scan then 7#u8
      else if occupied = 1#u32 then
        if sentinel = 0#u32 then 8#u8 else 0#u8
      else 0#u8
    else 1#u8
  else 1#u8

theorem extracted (first second : Bool) (occupied inverse sentinel : U32)
    (products : Array U32 3#usize) (scan : Bool) :
    PCI_ValidateRef.prefix first second occupied inverse sentinel products scan =
      ok (code first second occupied inverse sentinel products scan) := by
  unfold PCI_ValidateRef.prefix code
  simp only [PCF_ArrayIndex.result products 0#usize (by scalar_tac), PCF_ArrayIndex.result products 1#usize (by scalar_tac), PCF_ArrayIndex.result products 2#usize (by scalar_tac),bind_tc_ok,ok_ite]
  rfl

#print axioms ok_ite
#print axioms extracted
end PCI_ValidatePrefix
