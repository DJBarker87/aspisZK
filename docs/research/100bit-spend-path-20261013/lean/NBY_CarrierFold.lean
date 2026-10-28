import NBV_Audit
import KMX_CopyMeaning

set_option autoImplicit false
namespace AspisR1.NBY_CarrierFold

/-- A window source may depend on the actual prestate of that very step. -/
structure Window (α : Type) where
  base : Nat
  width : Nat
  source : (Nat → α) → Nat → α

def execute {α : Type} : List (Window α) → (Nat → α) → (Nat → α)
  | [], memory => memory
  | w::rest, memory => execute rest
      (KMX_CopyMeaning.loop (w.source memory) memory w.base w.width)

/-- Later windows consume the earlier windows' poststate, including their
source computation. This is the same-carrier composition, not independent runs. -/
theorem append_same_carrier {α : Type} (first second : List (Window α))
    (memory : Nat → α) :
    execute (first++second) memory = execute second (execute first memory) := by
  induction first generalizing memory with
  | nil => rfl
  | cons w rest ih =>
    exact ih (KMX_CopyMeaning.loop (w.source memory) memory w.base w.width)

/-- Pointwise arbitrary-coordinate native frames lift through any number of
windows, even when each next source depends on the preceding poststate. -/
theorem outside_frame {α : Type} (steps : List (Window α))
    (memory : Nat → α) (k : Nat)
    (outside : ∀ w ∈ steps, k < w.base ∨ w.base+w.width ≤ k) :
    execute steps memory k = memory k := by
  induction steps generalizing memory with
  | nil => rfl
  | cons w rest ih =>
    rw [execute, ih _ (fun v hv => outside v (List.mem_cons_of_mem w hv))]
    exact KMX_CopyMeaning.copy_frame (w.source memory) memory w.base w.width k
      (outside w (List.mem_cons_self))

#print axioms append_same_carrier
#print axioms outside_frame
end AspisR1.NBY_CarrierFold
