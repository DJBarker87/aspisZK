import PV_B3P_Install133
namespace PV_B3P_Extensionality133
open Aeneas Aeneas.Std
set_option autoImplicit false

-- A universally quantified valid index is equivalent to whole-vector equality.
-- The index is auxiliary; it places no restriction on the function input.
theorem vec_ext {α : Type} (a b : alloc.vec.Vec α)
    (hlen : a.val.length = b.val.length)
    (hget : ∀ (i : Nat) (ha : i < a.val.length) (hb : i < b.val.length),
      a.val[i] = b.val[i]) : a = b := by
  apply Subtype.ext
  exact List.ext_getElem hlen hget

theorem index_coverage (i : Nat) (hi : i < 214) :
    ∃ j : U8, j.val = i ∧ j.val < 214 := by
  have h256 : i < 256 := by omega
  exact ⟨U8.ofNatCore i h256, rfl, hi⟩

theorem vec_ext_214 {α : Type} (a b : alloc.vec.Vec α)
    (ha : a.val.length = 214) (hb : b.val.length = 214)
    (hget : ∀ (j : U8) (hj : j.val < 214),
      a.val[j.val]'(by omega) = b.val[j.val]'(by omega)) : a = b := by
  apply vec_ext a b (ha.trans hb.symm)
  intro i hai hbi
  have hi : i < 214 := by omega
  obtain ⟨j, hj, hjlt⟩ := index_coverage i hi
  simpa only [hj] using hget j hjlt

theorem auxiliary_domain_nonempty : ∃ j : U8, j.val < 214 := by
  exact ⟨0#u8, by scalar_tac⟩

#print axioms vec_ext
#print axioms index_coverage
#print axioms vec_ext_214
#print axioms auxiliary_domain_nonempty
end PV_B3P_Extensionality133
