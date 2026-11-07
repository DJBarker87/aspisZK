import PCI_ByteListComparison
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ByteArrayComparison

theorem eq {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b=ok (decide (a.val=b.val)) := by
  have h : a.length=b.length := a.property.trans b.property.symm
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos h]
  change List.allM PCI_ByteListComparison.compare (a.val.zip b.val)=_
  rw [PCI_ByteListComparison.all,PCI_ByteListComparison.zipped a.val b.val h]

theorem ne {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b=ok (decide (a.val≠b.val)) := by
  unfold core.array.equality.PartialEqArray.ne
  rw [eq]
  by_cases h : a.val=b.val <;> simp [h]

#print axioms eq
#print axioms ne
end PCI_ByteArrayComparison
