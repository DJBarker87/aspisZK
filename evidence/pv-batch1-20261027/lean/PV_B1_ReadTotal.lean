import PV_B1_ArrayRead
set_option autoImplicit false
namespace PV_B1_ReadTotal
open Aeneas Aeneas.Std Result

theorem read_total {T : Type} {n : Usize} (xs : Array T n) (i : Usize)
    (h : i.val<n.val) : ∃ v, Array.index_usize xs i = ok v := by
  have bound : i.val<xs.val.length := by rw [xs.property]; exact h
  exact ⟨_,PV_B1_ArrayRead.read xs i bound⟩

theorem bind_total {A B : Type} (r : Result A) (k : A → Result B)
    (hr : ∃ a, r=ok a) (hk : ∀ a, ∃ b, k a=ok b) :
    ∃ b, (do let a ← r; k a)=ok b := by
  obtain ⟨a,ha⟩ := hr
  rw [ha]
  exact hk a
#print axioms read_total
#print axioms bind_total
end PV_B1_ReadTotal
