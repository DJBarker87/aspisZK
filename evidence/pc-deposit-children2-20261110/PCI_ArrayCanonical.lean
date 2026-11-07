import PCI_DepositRef.Funs
import PCI_ValidatePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ArrayCanonical

def model (d : Array U32 8#usize) : Bool :=
  if d.val[0]!.val<2147483647 then if d.val[1]!.val<2147483647 then if d.val[2]!.val<2147483647 then if d.val[3]!.val<2147483647 then if d.val[4]!.val<2147483647 then if d.val[5]!.val<2147483647 then if d.val[6]!.val<2147483647 then decide (d.val[7]!.val<2147483647) else false else false else false else false else false else false else false

theorem extracted (d : Array U32 8#usize) : PCI_DepositRef.canonical d=ok (model d) := by
  unfold PCI_DepositRef.canonical model
  simp only [PCF_ArrayIndex.result d 0#usize (by scalar_tac),PCF_ArrayIndex.result d 1#usize (by scalar_tac),PCF_ArrayIndex.result d 2#usize (by scalar_tac),PCF_ArrayIndex.result d 3#usize (by scalar_tac),PCF_ArrayIndex.result d 4#usize (by scalar_tac),PCF_ArrayIndex.result d 5#usize (by scalar_tac),PCF_ArrayIndex.result d 6#usize (by scalar_tac),PCF_ArrayIndex.result d 7#usize (by scalar_tac),bind_tc_ok,PCI_ValidatePrefix.ok_ite]
  rfl

#print axioms extracted
end PCI_ArrayCanonical
