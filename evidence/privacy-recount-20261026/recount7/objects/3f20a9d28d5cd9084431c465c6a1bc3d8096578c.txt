import PV_B3_Forest_134_Funs
namespace PV_B3_MaskBump
open Aeneas Aeneas.Std Result
open PV_B3_Forest_134
set_option autoImplicit false

theorem zero : host_forest.mask_endpoint_bump 0#u8 = ok (some 1#u8) := by rfl
theorem one : host_forest.mask_endpoint_bump 1#u8 = ok (some 2#u8) := by rfl

theorem reject (n : U8) (h : 2#u8 ≤ n) :
    host_forest.mask_endpoint_bump n = ok none := by
  simp only [host_forest.mask_endpoint_bump, if_pos h]

theorem small_cases (n : U8) (h : n < 2#u8) : n = 0#u8 ∨ n = 1#u8 := by
  have hn : n.val < 2 := h
  have hs : n.val = 0 ∨ n.val = 1 := by omega
  rcases hs with hs | hs
  · exact Or.inl (UScalar.eq_of_val_eq hs)
  · exact Or.inr (UScalar.eq_of_val_eq hs)

theorem accept (n : U8) (h : n < 2#u8) :
    ∃ next : U8, host_forest.mask_endpoint_bump n = ok (some next) ∧
      next.val = n.val + 1 ∧ next.val ≤ 2 := by
  rcases small_cases n h with rfl | rfl
  · exact ⟨1#u8, zero, rfl, by decide⟩
  · exact ⟨2#u8, one, rfl, by decide⟩

#print axioms zero
#print axioms one
#print axioms reject
#print axioms small_cases
#print axioms accept
end PV_B3_MaskBump
