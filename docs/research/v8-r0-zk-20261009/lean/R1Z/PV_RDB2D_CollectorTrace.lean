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

def alignmentWord : core.ptr.alignment.Alignment → Nat
  | ._Align1Shl0 => 2^0
  | ._Align1Shl1 => 2^1
  | ._Align1Shl2 => 2^2
  | ._Align1Shl3 => 2^3
  | ._Align1Shl4 => 2^4
  | ._Align1Shl5 => 2^5
  | ._Align1Shl6 => 2^6
  | ._Align1Shl7 => 2^7
  | ._Align1Shl8 => 2^8
  | ._Align1Shl9 => 2^9
  | ._Align1Shl10 => 2^10
  | ._Align1Shl11 => 2^11
  | ._Align1Shl12 => 2^12
  | ._Align1Shl13 => 2^13
  | ._Align1Shl14 => 2^14
  | ._Align1Shl15 => 2^15
  | ._Align1Shl16 => 2^16
  | ._Align1Shl17 => 2^17
  | ._Align1Shl18 => 2^18
  | ._Align1Shl19 => 2^19
  | ._Align1Shl20 => 2^20
  | ._Align1Shl21 => 2^21
  | ._Align1Shl22 => 2^22
  | ._Align1Shl23 => 2^23
  | ._Align1Shl24 => 2^24
  | ._Align1Shl25 => 2^25
  | ._Align1Shl26 => 2^26
  | ._Align1Shl27 => 2^27
  | ._Align1Shl28 => 2^28
  | ._Align1Shl29 => 2^29
  | ._Align1Shl30 => 2^30
  | ._Align1Shl31 => 2^31
  | ._Align1Shl32 => 2^32
  | ._Align1Shl33 => 2^33
  | ._Align1Shl34 => 2^34
  | ._Align1Shl35 => 2^35
  | ._Align1Shl36 => 2^36
  | ._Align1Shl37 => 2^37
  | ._Align1Shl38 => 2^38
  | ._Align1Shl39 => 2^39
  | ._Align1Shl40 => 2^40
  | ._Align1Shl41 => 2^41
  | ._Align1Shl42 => 2^42
  | ._Align1Shl43 => 2^43
  | ._Align1Shl44 => 2^44
  | ._Align1Shl45 => 2^45
  | ._Align1Shl46 => 2^46
  | ._Align1Shl47 => 2^47
  | ._Align1Shl48 => 2^48
  | ._Align1Shl49 => 2^49
  | ._Align1Shl50 => 2^50
  | ._Align1Shl51 => 2^51
  | ._Align1Shl52 => 2^52
  | ._Align1Shl53 => 2^53
  | ._Align1Shl54 => 2^54
  | ._Align1Shl55 => 2^55
  | ._Align1Shl56 => 2^56
  | ._Align1Shl57 => 2^57
  | ._Align1Shl58 => 2^58
  | ._Align1Shl59 => 2^59
  | ._Align1Shl60 => 2^60
  | ._Align1Shl61 => 2^61
  | ._Align1Shl62 => 2^62
  | ._Align1Shl63 => 2^63

def alignment2 : core.ptr.alignment.Alignment := ._Align1Shl1

theorem alignment2_word : alignmentWord alignment2=2 := rfl

def publicRequest (r : Request) : Action :=
  if r.oldCapacity=0 then .allocate (r.newCapacity*r.shape.width) (alignmentWord r.shape.align)
  else .reallocate (r.oldCapacity*r.shape.width) (alignmentWord r.shape.align) (r.newCapacity*r.shape.width)

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
  ok { state with
    resource := { state.resource with
      allocator := s
      deallocCalls := state.resource.deallocCalls+1
      live := fun a => if a=address then false else state.resource.live a }
    trace := state.trace++[.deallocate bytes 2]
    initialized := fun a => if a=address then none else state.initialized a }


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
        {state with
          resource := (reference (fun _ _ => decision) wordMax byteMax shape b additional state.resource).world
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
        {state with
          resource := attempted ⟨b.address,b.capacity,b.values.length+additional,shape⟩ none s state.resource
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

#print axioms alignment2_word
#print axioms issue_reserve_family
#print axioms issue_null
#print axioms abort_prefix
#print axioms release_layout
#print axioms no_spare_initialization
end R1Z.PV_RDB2D_CollectorTrace
