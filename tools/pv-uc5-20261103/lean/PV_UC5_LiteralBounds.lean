import Aeneas
open Aeneas Aeneas.Std
namespace PV_UC5_LiteralBounds
-- Expose the short character list, never normalize the machine-word maximum.
theorem abc_size : "abc".toByteArray.size = 3 := by
  change (String.ofList ['a', 'b', 'c']).toByteArray.size = 3
  rfl
theorem short_bound (s : String) (n : Nat) (h : s.toByteArray.size = n)
    (hn : n ≤ 64) : s.toByteArray.size ≤ U32.max := by
  rw [h, U32.max_eq]
  omega
#print axioms abc_size
#print axioms short_bound
end PV_UC5_LiteralBounds
