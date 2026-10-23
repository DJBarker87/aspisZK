import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6StdByteArray

private theorem allM_total {T : Type} (f : T → Result Bool)
    (hf : ∀ x, ∃ b, f x=ok b) (xs : List T) :
    ∃ b, List.allM f xs=ok b := by
  induction xs with
  | nil => exact ⟨true,rfl⟩
  | cons x xs ih =>
    obtain ⟨b,hb⟩ := hf x
    simp only [List.allM,hb,bind_tc_ok]
    cases b
    · exact ⟨false,rfl⟩
    · exact ih

/-- TOTAL primitive byte-array comparison for every native array extent. -/
theorem eq_total {N : Usize} (a b : Array U8 N) :
    ∃ result, core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b=ok result := by
  unfold core.array.equality.PartialEqArray.eq
  split
  · apply allM_total
    intro pair
    rcases pair with ⟨x,y⟩
    exact ⟨_,rfl⟩
  · exact ⟨false,rfl⟩

@[step] theorem eq_spec {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ _ => True ⦄ := by
  obtain ⟨result,h⟩ := eq_total a b
  rw [h,WP.spec_ok]
  trivial

#print axioms eq_total
#print axioms eq_spec
end AspisS6StdByteArray
