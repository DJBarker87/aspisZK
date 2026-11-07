import PCI_DepositRef.Funs
import PCI_ValidatePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ArrayCanonical

def model (d : Array U32 8#usize) : Bool :=
  decide (d.val[0]!.val<2147483647) && decide (d.val[1]!.val<2147483647) &&
  decide (d.val[2]!.val<2147483647) && decide (d.val[3]!.val<2147483647) &&
  decide (d.val[4]!.val<2147483647) && decide (d.val[5]!.val<2147483647) &&
  decide (d.val[6]!.val<2147483647) && decide (d.val[7]!.val<2147483647)

theorem extracted (d : Array U32 8#usize) : PCI_DepositRef.canonical d=ok (model d) := by
  unfold PCI_DepositRef.canonical model
  simp only [PCF_ArrayIndex.result d 0#usize (by scalar_tac),PCF_ArrayIndex.result d 1#usize (by scalar_tac),PCF_ArrayIndex.result d 2#usize (by scalar_tac),PCF_ArrayIndex.result d 3#usize (by scalar_tac),PCF_ArrayIndex.result d 4#usize (by scalar_tac),PCF_ArrayIndex.result d 5#usize (by scalar_tac),PCF_ArrayIndex.result d 6#usize (by scalar_tac),PCF_ArrayIndex.result d 7#usize (by scalar_tac),bind_tc_ok,PCI_ValidatePrefix.ok_ite]
  split <;> simp_all only [decide_true,decide_false,Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true,ite_true,ite_false]
  all_goals repeat' first | split | simp_all

#print axioms extracted
end PCI_ArrayCanonical
