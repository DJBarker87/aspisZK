import NFB_ZeroScan
import KMX_CopyMeaning
set_option autoImplicit false
namespace NFB_PhysicalFrame
open Aeneas.Std

/-- Allocation identities, rather than equal contents, select physical places.
The interpretation of these identities in native memory is P6. -/
abbrev Heap := Nat → Option (List U32)

def write (heap : Heap) (owner : Nat) (value : Option (List U32)) : Heap :=
  fun place => if place=owner then value else heap place

inductive Action where
 | allocate (owner : Nat) (value : List U32)
 | store (owner offset : Nat) (value : U32)
 | append (owner : Nat) (values : List U32)
 | release (owner : Nat)

def Action.owner : Action → Nat
 | .allocate o _ | .store o _ _ | .append o _ | .release o => o

def Action.apply (action : Action) (heap : Heap) : Heap :=
 match action with
 | .allocate o v => write heap o (some v)
 | .store o j v => write heap o ((heap o).map (fun xs => xs.set j v))
 | .append o v => write heap o ((heap o).map (fun xs => xs++v))
 | .release o => write heap o none

def run : List Action → Heap → Heap
 | [],heap => heap
 | action::tail,heap => run tail (action.apply heap)

theorem other_place (action : Action) (heap : Heap) (place : Nat)
    (disjoint : place ≠ action.owner) : action.apply heap place=heap place := by
 cases action <;> simp only [Action.apply,Action.owner] at * <;>
   simp only [write,disjoint,if_false]

/-- No update, allocation or release in the actual ordered private-buffer
trace can change the protected allocation. Repeated writes keep SAME identity. -/
theorem trace_frame (actions : List Action) (heap : Heap) (place : Nat)
    (disjoint : ∀ a ∈ actions, place≠a.owner) : run actions heap place=heap place := by
 induction actions generalizing heap with
 | nil => rfl
 | cons action tail ih =>
   rw [run,ih (action.apply heap) (fun a ha => disjoint a (List.mem_cons_of_mem action ha))]
   exact other_place action heap place (disjoint action (List.mem_cons_self))

/-- Extensional observation of the SAME owner reconstructs its whole payload;
a separately selected buffer with equal length is insufficient. -/
theorem same_payload (heap : Heap) (owner : Nat) (before after : List U32)
    (selected : heap owner=some after) (size : after.length=before.length)
    (windows : ∀ j, j<before.length → after[j]?=before[j]?) :
    heap owner=some before := by
 have same : after=before := by
  apply List.ext_getElem?
  intro j
  by_cases h : j<before.length
  · exact windows j h
  · rw [List.getElem?_eq_none (by omega : after.length≤j),
      List.getElem?_eq_none (by omega : before.length≤j)]
 rw [selected,same]

/-- Frame transport also covers a rejected finite prefix; no accepted-only
restriction is used. -/
theorem prefix_frame (actions : List Action) (heap : Heap) (place count : Nat)
    (disjoint : ∀ a ∈ actions, place≠a.owner) :
    run (actions.take count) heap place=heap place := by
 apply trace_frame
 intro a ha
 exact disjoint a (List.mem_of_mem_take ha)

#print axioms other_place
#print axioms trace_frame
#print axioms same_payload
#print axioms prefix_frame
end NFB_PhysicalFrame
