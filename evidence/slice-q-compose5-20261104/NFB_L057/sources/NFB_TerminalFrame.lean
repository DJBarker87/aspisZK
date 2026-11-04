import NFB_ReverseTrace
import NFB_CollectAssociation
set_option autoImplicit false
namespace NFB_TerminalFrame
open Aeneas.Std AspisR1 NFB_PhysicalFrame NFB_PrivateFrame

def resize : Nat → List Action
 | 0 => []
 | n+1 => append .inverse [0#u32] :: resize n

def collect : List (Array U32 5#usize) → List Action
 | [] => []
 | row::rs => append .rows row.val :: collect rs

def actions (flat prefixes : List U32) (suffix : U32) (count : Nat)
 (groups : List (Array U32 5#usize)) : List Action :=
 [allocate .prefixes prefixes,allocate .inverse []]++resize count++
 NFB_ReverseTrace.writes flat prefixes count suffix++
 [allocate .rows []]++collect groups++
 [release .inverse,release .prefixes,release .flat]

theorem resize_owned (n : Nat) : ∀ a∈resize n,Private a := by
 induction n with
 | zero => simp [resize]
 | succ n ih =>
  intro a ha
  simp only [resize,List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Private.append _ _
  · exact ih a ha

theorem collect_owned (groups : List (Array U32 5#usize)) : ∀ a∈collect groups,Private a := by
 induction groups with
 | nil => simp [collect]
 | cons row rs ih =>
  intro a ha
  simp only [collect,List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Private.append _ _
  · exact ih a ha

theorem owned (flat prefixes : List U32) (suffix : U32) (count : Nat)
 (groups : List (Array U32 5#usize)) :
 ∀ a∈actions flat prefixes suffix count groups,Private a := by
 intro a ha
 simp only [actions,List.mem_append] at ha
 rcases ha with ((((h0 | hr) | hw) | hrow) | hc) | hrel
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at h0
   rcases h0 with rfl | rfl <;> exact Private.allocate _ _
 · exact resize_owned count a hr
 · exact NFB_ReverseTrace.owned flat prefixes count suffix a hw
 · simp only [List.mem_singleton] at hrow
   subst a
   exact Private.allocate _ _
 · exact collect_owned groups a hc
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hrel
   rcases hrel with rfl | rfl | rfl <;> exact Private.release _

theorem query_frame (flat prefixes : List U32) (suffix : U32) (count : Nat)
 (groups : List (Array U32 5#usize)) (heap : Heap) (countTaken : Nat) :
 NFB_PhysicalFrame.run ((actions flat prefixes suffix count groups).take countTaken) heap 0=heap 0 :=
 protected_query _ heap countTaken (owned flat prefixes suffix count groups)
#print axioms resize_owned
#print axioms collect_owned
#print axioms owned
#print axioms query_frame
end NFB_TerminalFrame
end
