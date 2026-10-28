import PV_B3P_Extensionality133
namespace PV_B3P_ByteExtensionality226
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem index_coverage (n i : Nat) (hn : n ≤ 1472) (hi : i < n) :
    ∃ j : U16, j.val = i ∧ j.val < n := by
  have h65536 : i < 65536 := by omega
  exact ⟨U16.ofNatCore i h65536, rfl, hi⟩

theorem vec_ext {α : Type} (n : Nat) (hn : n ≤ 1472) (a b : alloc.vec.Vec α)
    (ha : a.val.length = n) (hb : b.val.length = n)
    (hget : ∀ (j : U16) (hj : j.val < n),
      a.val[j.val]'(by omega) = b.val[j.val]'(by omega)) : a = b := by
  apply PV_B3P_Extensionality133.vec_ext a b (ha.trans hb.symm)
  intro i hai hbi
  have hi : i < n := by omega
  obtain ⟨j, hj, hjlt⟩ := index_coverage n i hn hi
  simpa only [hj] using hget j hjlt

#print axioms index_coverage
#print axioms vec_ext
end PV_B3P_ByteExtensionality226
