import R1Z.PV_RDB2C_PV_RDB1_V183
import R1Z.PV_RDB2D_CollectorShape
namespace R1Z.PV_RDB2D_CollectorTrace
open Aeneas Aeneas.Std Result
open PV_RDB1_V183_ReserveWorld
set_option autoImplicit false

inductive Action where
  | allocate (bytes align : Nat)
  | reallocate (oldBytes align newBytes : Nat)
  | deallocate (bytes align : Nat)
  | abort (bytes align : Nat)
  deriving DecidableEq, Repr

inductive Cells where
  | links (values : List PV_B3P_Schedule133.Link)
  | rows (values : List Nat)

structure State (S F : Type) where
  resource : World S F
  trace : List Action
  initialized : Nat → Option Cells

/-- This hook is the existing runtime/allocator primitive boundary. Its null
outcome and private post-state are explicit. It may also fail or diverge. -/
abbrev Allocator (S : Type) := Request → S → Result (Option Nat × S)

def publicRequest (r : Request) : Action :=
  if r.oldCapacity=0 then .allocate (r.newCapacity*r.shape.width) 2
  else .reallocate (r.oldCapacity*r.shape.width) 2 (r.newCapacity*r.shape.width)

/-- Uses the proved reserve family's finish, with the actual primitive result.
Only the public size/alignment projection is added to the original world. -/
def issue {T S F : Type} (allocate : Allocator S) (shape : Shape)
    (b : Buffer T) (additional : Nat) (state : State S F) :
    Result (Execution T S F × State S F) := do
  let req : Request := ⟨b.address,b.capacity,b.values.length+additional,shape⟩
  let decision ← allocate req state.resource.allocator
  let out := finish (fun _ _ => decision) shape b additional state.resource
  ok (out,{state with resource := out.world, trace := state.trace++[publicRequest req]})

/-- The actual handle_alloc_error continuation is passed the complete world
at the null edge. No destructor suffix is run before this continuation. -/
def abortWith {S F A : Type} (handler : Action → State S F → Result A)
    (bytes : Nat) (state : State S F) : Result A :=
  handler (.abort bytes 2) {state with trace := state.trace++[.abort bytes 2]}

def release {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (address bytes : Nat) (state : State S F) : Result (State S F) := do
  let s ← deallocate address bytes 2 state.resource.allocator
  ok {state with resource := {state.resource with allocator := s,
       deallocCalls := state.resource.deallocCalls+1,
       live := fun a => if a=address then false else state.resource.live a},
       trace := state.trace++[.deallocate bytes 2],
       initialized := fun a => if a=address then none else state.initialized a}

/-- A typed write changes only the owned object's initialized prefix; spare
capacity is not fabricated as initialized data. -/
def store {S F : Type} (address : Nat) (cells : Cells) (state : State S F) : State S F :=
  {state with initialized := fun a => if a=address then some cells else state.initialized a}

def empty (T : Type) : Buffer T := ⟨2,0,[],by rfl⟩

theorem issue_reserve_family {T S F : Type} (allocate : Allocator S) (shape : Shape)
    (b : Buffer T) (additional wordMax byteMax : Nat) (state : State S F)
    (grow : additional > b.capacity-b.values.length) (width : shape.width ≠ 0)
    (words : b.values.length+additional ≤ wordMax)
    (bytes : (b.values.length+additional)*shape.width ≤ byteMax)
    (decision : Option Nat × S)
    (h : allocate ⟨b.address,b.capacity,b.values.length+additional,shape⟩ state.resource.allocator = ok decision) :
    issue allocate shape b additional state =
      ok (reference (fun _ _ => decision) wordMax byteMax shape b additional state.resource,
        {state with resource := (reference (fun _ _ => decision) wordMax byteMax shape b additional state.resource).world,
          trace := state.trace++[publicRequest ⟨b.address,b.capacity,b.values.length+additional,shape⟩]}) := by
  have eq := source_reference (fun (_ : Request) (_ : S) => decision)
    wordMax byteMax shape b additional state.resource
  have ng : ¬b.values.length+additional>wordMax := by omega
  have nb : ¬(b.values.length+additional)*shape.width>byteMax := by omega
  simp only [native,growExact,grow,width,ng,nb,ite_true,ite_false] at eq
  simp only [issue,h,bind_tc_ok]
  rw [←eq]

theorem issue_null {T S F : Type} (allocate : Allocator S) (shape : Shape)
    (b : Buffer T) (additional : Nat) (state : State S F) (s : S)
    (h : allocate ⟨b.address,b.capacity,b.values.length+additional,shape⟩ state.resource.allocator = ok (none,s)) :
    issue allocate shape b additional state =
      ok (finish (fun _ _ => (none,s)) shape b additional state.resource,
        {state with resource := attempted ⟨b.address,b.capacity,b.values.length+additional,shape⟩ none s state.resource,
          trace := state.trace++[publicRequest ⟨b.address,b.capacity,b.values.length+additional,shape⟩]}) := by
  simp only [issue,h,bind_tc_ok,finish]

/-- Arbitrary incoming trace and private runtime state remain visible at the
handler; failure does not imply successful allocation or erase live storage. -/
theorem abort_prefix {S F A : Type} (handler : Action → State S F → Result A)
    (bytes : Nat) (state : State S F) :
    abortWith handler bytes state =
      handler (.abort bytes 2) {state with trace := state.trace++[.abort bytes 2]} := rfl

theorem release_layout {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (address bytes : Nat) (state : State S F) (s : S)
    (h : deallocate address bytes 2 state.resource.allocator=ok s) :
    (do let after ← release deallocate address bytes state; ok after.trace) =
      ok (state.trace++[.deallocate bytes 2]) := by
  simp only [release,h,bind_tc_ok]

theorem no_spare_initialization {S F : Type} (address other : Nat) (cells : Cells)
    (state : State S F) (h : other ≠ address) :
    (store address cells state).initialized other=state.initialized other := by
  simp only [store,h,ite_false]

#print axioms issue_reserve_family
#print axioms issue_null
#print axioms abort_prefix
#print axioms release_layout
#print axioms no_spare_initialization
end R1Z.PV_RDB2D_CollectorTrace
