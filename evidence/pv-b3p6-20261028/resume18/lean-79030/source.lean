import PV_B3P_Success227
import PV_B3P_Ordered227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_Success227
set_option autoImplicit false

/-- Fixed four-cell from_fn/array-map callback schedule. -/
def from_fn_four550 {α : Type} (f : Usize → Result α) : Result (Array α 4#usize) := do
  let a ← f 0#usize
  let b ← f 1#usize
  let c ← f 2#usize
  let d ← f 3#usize
  .ok (Array.make 4#usize [a,b,c,d] (by simp only [List.length_cons,List.length_nil]; rfl))

theorem from_fn_four_congr550 {α : Type} (f g : Usize → Result α)
    (same : ∀ i, i.val < 4 → f i = g i) :
    from_fn_four550 f = from_fn_four550 g := by
  unfold from_fn_four550
  rw [same 0#usize (by decide), same 1#usize (by decide),
    same 2#usize (by decide), same 3#usize (by decide)]

theorem from_fn_four_total550 {α : Type} (f : Usize → Result α)
    (total : ∀ i, i.val < 4 → Success (f i)) :
    Success (from_fn_four550 f) := by
  obtain ⟨a,ha⟩ := total 0#usize (by decide)
  obtain ⟨b,hb⟩ := total 1#usize (by decide)
  obtain ⟨c,hc⟩ := total 2#usize (by decide)
  obtain ⟨d,hd⟩ := total 3#usize (by decide)
  unfold from_fn_four550
  rw [ha,hb,hc,hd]
  exact ok _

/-- Only a proved total ignored computation may be removed. -/
theorem ignored_total_continuation550 {α β : Type} (r : Result α)
    (total : Success r) (next : Result β) :
    (do let _ ← r; next) = next := by
  obtain ⟨value,equal⟩ := total
  rw [equal]
  rfl

#print axioms from_fn_four_congr550
#print axioms from_fn_four_total550
#print axioms ignored_total_continuation550
end PV_B3P_Association550227
