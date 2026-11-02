import NEO_FixedWindow
set_option autoImplicit false
namespace NEO_WindowRelocation
open Aeneas Aeneas.Std Result

theorem selected_values {T : Type} (src dst : Nat → T) (source target width : Nat) :
 (List.range width).map (fun j => NEO_WindowFrame.relocated src dst source target width (target+j)) =
 (List.range width).map (fun j => src (source+j)) := by
 apply List.map_congr_left
 intro j member
 exact NEO_WindowFrame.selected _ _ _ _ _ _ (List.mem_range.mp member)

theorem disjoint {T : Type} (a b dst : Nat → T) (oa ob ta tb na nb j : Nat)
 (apart : ta+na≤tb ∨ tb+nb≤ta) (inside : j<na) :
 NEO_WindowFrame.relocated b (NEO_WindowFrame.relocated a dst oa ta na) ob tb nb (ta+j)=a (oa+j) := by
 rw [NEO_WindowFrame.outside _ _ _ _ _ _ (by omega)]
 exact NEO_WindowFrame.selected _ _ _ _ _ _ inside

theorem same_selected {T : Type} (a b da db : Nat → T) (oa ob ta tb n : Nat)
 (same : ∀ j, j<n → a (oa+j)=b (ob+j)) :
 (List.range n).map (fun j => NEO_WindowFrame.relocated a da oa ta n (ta+j)) =
 (List.range n).map (fun j => NEO_WindowFrame.relocated b db ob tb n (tb+j)) := by
 apply List.map_congr_left
 intro j member
 exact NEO_WindowFrame.rebase _ _ _ _ _ _ _ _ _ same j (List.mem_range.mp member)

#print axioms selected_values
#print axioms disjoint
#print axioms same_selected
end NEO_WindowRelocation
