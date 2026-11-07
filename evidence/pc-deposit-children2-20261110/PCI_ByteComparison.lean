import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ByteComparison

theorem ne (x y : U8) : core.cmp.PartialEqU8.ne x y=ok (decide (x≠y)) := by
  simp only [core.cmp.PartialEqU8,liftFun2,core.cmp.impls.PartialEqU8.ne,lift]

theorem eq (x y : U8) : core.cmp.PartialEqU8.eq x y=ok (decide (x=y)) := by
  simp only [core.cmp.PartialEqU8,liftFun2,core.cmp.impls.PartialEqU8.eq,lift]

#print axioms ne
#print axioms eq
end PCI_ByteComparison
