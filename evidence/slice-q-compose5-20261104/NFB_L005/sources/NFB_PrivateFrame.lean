import NFB_PhysicalFrame
set_option autoImplicit false
namespace NFB_PrivateFrame
open Aeneas.Std NFB_PhysicalFrame

/-- Private allocation slots cannot designate the root's protected query place.
The native interpretation maps these slots to fresh owned allocations. -/
inductive Place where
 | flat | lines | prefixes | inverse | rows
 deriving DecidableEq

def Place.id : Place → Nat
 | .flat => 1 | .lines => 2 | .prefixes => 3 | .inverse => 4 | .rows => 5

def allocate (place : Place) (value : List U32) : Action := .allocate place.id value
def store (place : Place) (offset : Nat) (value : U32) : Action := .store place.id offset value
def append (place : Place) (value : List U32) : Action := .append place.id value
def release (place : Place) : Action := .release place.id

inductive Private : Action → Prop where
 | allocate (p : Place) (v : List U32) : Private (allocate p v)
 | store (p : Place) (j : Nat) (v : U32) : Private (store p j v)
 | append (p : Place) (v : List U32) : Private (append p v)
 | release (p : Place) : Private (release p)

theorem disjoint (a : Action) (h : Private a) : 0≠a.owner := by
 cases h <;> rename_i p <;> cases p <;> decide

/-- Any prefix, including one ending at a rejection, preserves the SAME
protected query allocation. This is the ownership induction, not a native
receipt; the source/trace association must separately instantiate Private. -/
theorem protected_query (actions : List Action) (heap : Heap) (count : Nat)
    (private : ∀ a∈actions, Private a) :
    run (actions.take count) heap 0=heap 0 := by
 apply prefix_frame
 intro a ha
 exact disjoint a (private a ha)

#print axioms disjoint
#print axioms protected_query
end NFB_PrivateFrame
