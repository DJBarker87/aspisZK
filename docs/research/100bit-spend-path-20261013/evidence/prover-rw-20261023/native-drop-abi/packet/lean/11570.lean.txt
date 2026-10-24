import Aeneas

namespace ProverRwNativeDropABI

/-- Full values carry their nested reference identities; H is the untouched heap.
The temporary is explicit and ends at Bottom. This does not model destructors. -/
def moveSwap {V H : Type} (left right : V) (heap : H) : V × V × H × Option V :=
  let tmp := left
  let left := right
  let right := tmp
  (left, right, heap, none)

theorem moveSwap_relation {V H : Type} (left right : V) (heap : H) :
    moveSwap left right heap = (right, left, heap, none) := rfl

/-- Both directions use the existing permutation model, with independent
forward/backward carriers. No value of a nested referent is manufactured. -/
def forward {F : Type} (p : F × F) : F × F :=
  Aeneas.Std.core.mem.swap p.1 p.2

def backward {B : Type} (p : B × B) : B × B :=
  Aeneas.Std.core.mem.swap p.1 p.2

theorem model_relation {V H : Type} (a b : V) (heap : H) :
    moveSwap a b heap = ((forward (a,b)).1, (forward (a,b)).2, heap, none) := rfl

/-- Arbitrary callback, backward carrier, and full state: inverse permutation
routes the whole updated owner/heap relation, rather than an output number. -/
theorem callback_relation {F B H : Type}
    (k : (F × F) × H → (B × B) × H) (a b : F) (heap : H) :
    let out := k (forward (a,b),heap)
    (backward out.1, out.2) = ((out.1.2,out.1.1),out.2) := rfl

theorem backward_involution {B : Type} (p : B × B) :
    backward (backward p) = p := by cases p; rfl

#print moveSwap_relation
#print model_relation
#print callback_relation
#print backward_involution
#print axioms moveSwap_relation
#print axioms model_relation
#print axioms callback_relation
#print axioms backward_involution
end ProverRwNativeDropABI
