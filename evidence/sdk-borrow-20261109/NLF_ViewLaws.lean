import NLF_WrapperLaws
set_option autoImplicit false
namespace NLF_ViewLaws
open NLF_RefCell NLF_SdkModel
structure Projection (α : Type) where
  guard : Guard
  project : Payload → α

def read {α : Type} (s : State) (v : Projection α) := v.project (deref s v.guard)

def map {α β : Type} (v : Projection α) (f : α → β) : Projection β :=
  ⟨v.guard,f ∘ v.project⟩

def write (s : State) (g : Guard) (v : Payload) : State :=
  put s g.cell {s.cells g.cell with payload := v}

theorem map_token {α β : Type} (v : Projection α) (f : α → β) : (map v f).guard = v.guard := rfl

theorem map_read {α β : Type} (s : State) (v : Projection α) (f : α → β) :
    read s (map v f) = f (read s v) := rfl

theorem map_release {α β : Type} (s : State) (v : Projection α) (f : α → β) :
    release s (map v f).guard = release s v.guard := rfl

theorem write_deref (s : State) (g : Guard) (v : Payload) : deref (write s g v) g = v := by
  simp [write,deref,put]

theorem write_frame (s : State) (g : Guard) (v : Payload) (i : Nat) (h : i≠g.cell) :
    (write s g v).cells i = s.cells i := by simp [write,put,h]

theorem write_counter (s : State) (g : Guard) (v : Payload) (i : Nat) :
    flag ((write s g v).cells i) = flag (s.cells i) := by
  by_cases h : i=g.cell <;> simp [write,put,h,flag]

theorem write_liveness (s : State) (g : Guard) (v : Payload) (t i : Nat) (k : Kind) :
    live ((write s g v).cells i) t k ↔ live (s.cells i) t k := by
  by_cases h : i=g.cell <;> cases k <;> simp [write,put,h,live]

#print axioms map_token
#print axioms map_read
#print axioms map_release
#print axioms write_deref
#print axioms write_frame
#print axioms write_counter
#print axioms write_liveness
end NLF_ViewLaws
