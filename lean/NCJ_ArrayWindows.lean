import NCJ_GuardExact
set_option autoImplicit false
namespace NCJ_ArrayWindows
open Aeneas Aeneas.Std

theorem ext {α : Type} {n : Usize} (a b : Array α n)
    (same : ∀ i (h : i<n.val),NCJ_GuardExact.pick a i h=NCJ_GuardExact.pick b i h) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro i hi hj
    have bound : i<n.val := by rw [←a.property];exact hi
    exact same i bound

/-- Assemble nested factor windows without reducing a concrete 5x5x4 array. -/
theorem factor_ext {α : Type}
    (a b : Array (Array (Array α 4#usize) 5#usize) 5#usize)
    (same : ∀ (k d : Fin 5) (lane : Fin 4),
      NCJ_GuardExact.pick (NCJ_GuardExact.pick (NCJ_GuardExact.pick a k.val k.isLt) d.val d.isLt) lane.val lane.isLt =
      NCJ_GuardExact.pick (NCJ_GuardExact.pick (NCJ_GuardExact.pick b k.val k.isLt) d.val d.isLt) lane.val lane.isLt) : a=b := by
  apply ext
  intro k hk
  apply ext
  intro d hd
  apply ext
  intro lane hl
  exact same ⟨k,hk⟩ ⟨d,hd⟩ ⟨lane,hl⟩

theorem points_ext {α : Type} (a b : Array (Array α 10#usize) 3#usize)
    (same : ∀ (k : Fin 3) (coordinate : Fin 10),
      NCJ_GuardExact.pick (NCJ_GuardExact.pick a k.val k.isLt) coordinate.val coordinate.isLt =
      NCJ_GuardExact.pick (NCJ_GuardExact.pick b k.val k.isLt) coordinate.val coordinate.isLt) : a=b := by
  apply ext
  intro k hk
  apply ext
  intro coordinate hc
  exact same ⟨k,hk⟩ ⟨coordinate,hc⟩

#print axioms ext
#print axioms factor_ext
#print axioms points_ext
end NCJ_ArrayWindows
