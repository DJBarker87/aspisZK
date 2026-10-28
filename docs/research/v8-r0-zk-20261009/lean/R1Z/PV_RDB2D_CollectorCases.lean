import R1Z.PV_RDB2D_CollectorProgram
namespace R1Z.PV_RDB2D_CollectorCases
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld
open PV_RDB2D_CollectorTrace PV_RDB2D_CollectorProgram
set_option autoImplicit false

def afterRequest {S F : Type} (r : Request) (p : Option Nat) (s : S)
    (state : State S F) : State S F :=
  let w := attempted r p s state.resource
  {state with resource := match p with | none => w | some a => succeeded r a w,
    trace := state.trace++[publicRequest r]}

theorem success {T S F : Type} (allocate : Allocator S) (handler : Handler S F)
    (shape : Shape) (b : Buffer T) (n : Nat) (state : State S F)
    (next : Nat → State S F → Result (Returned × State S F)) (p : Nat) (s : S)
    (h : allocate ⟨b.address,b.capacity,b.values.length+n,shape⟩ state.resource.allocator=ok (some p,s)) :
    request allocate handler shape b n state next =
      next p (afterRequest ⟨b.address,b.capacity,b.values.length+n,shape⟩ (some p) s state) := by
  simp only [request,issue,h,bind_tc_ok,finish,afterRequest]

theorem null {T S F : Type} (allocate : Allocator S) (handler : Handler S F)
    (shape : Shape) (b : Buffer T) (n : Nat) (state : State S F)
    (next : Nat → State S F → Result (Returned × State S F)) (s : S)
    (h : allocate ⟨b.address,b.capacity,b.values.length+n,shape⟩ state.resource.allocator=ok (none,s)) :
    request allocate handler shape b n state next =
      abortWith handler ((b.values.length+n)*shape.width)
        (afterRequest ⟨b.address,b.capacity,b.values.length+n,shape⟩ none s state) := by
  simp only [request,issue,h,bind_tc_ok,finish,afterRequest]

theorem primitive_fail {T S F : Type} (allocate : Allocator S) (handler : Handler S F)
    (shape : Shape) (b : Buffer T) (n : Nat) (state : State S F)
    (next : Nat → State S F → Result (Returned × State S F)) (e : Aeneas.Std.Error)
    (h : allocate ⟨b.address,b.capacity,b.values.length+n,shape⟩ state.resource.allocator=fail e) :
    request allocate handler shape b n state next=fail e := by
  simp only [request,issue,h,bind_tc_fail]

theorem primitive_div {T S F : Type} (allocate : Allocator S) (handler : Handler S F)
    (shape : Shape) (b : Buffer T) (n : Nat) (state : State S F)
    (next : Nat → State S F → Result (Returned × State S F))
    (h : allocate ⟨b.address,b.capacity,b.values.length+n,shape⟩ state.resource.allocator=div) :
    request allocate handler shape b n state next=div := by
  simp only [request,issue,h,bind_tc_div]

theorem first_null {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) (s : S)
    (h : allocate ⟨2,0,127,⟨8,alignment2⟩⟩ state.resource.allocator=ok (none,s)) :
    source allocate deallocate handler state =
      handler (.abort 1016 2)
        {afterRequest ⟨2,0,127,⟨8,alignment2⟩⟩ none s state with
          trace := state.trace++[.allocate 1016 2,.abort 1016 2]} := by
  rw [PV_RDB2D_CollectorProgram.complete]
  unfold PV_RDB2D_CollectorProgram.reference
  rw [null allocate handler _ _ _ _ _ s h]
  simp only [empty,List.length_nil,Nat.zero_add,abortWith,afterRequest,publicRequest,
    alignment2_word,show (127:Nat)*8=1016 by rfl,show (0:Nat)=0 by rfl,ite_true,
    List.append_assoc,List.cons_append,List.nil_append]

theorem null_keeps_allocated_storage {S F : Type} (r : Request) (s : S) (state : State S F) :
    (afterRequest r none s state).resource.memory=state.resource.memory ∧
    (afterRequest r none s state).resource.live=state.resource.live ∧
    (afterRequest r none s state).initialized=state.initialized ∧
    (afterRequest r none s state).resource.allocator=s := by
  simp only [afterRequest,attempted,and_self]

theorem stored_prefix {S F : Type} (a : Nat) (cells : Cells) (state : State S F) :
    (store a cells state).initialized a=some cells := by simp only [store,ite_true]

#print axioms success
#print axioms null
#print axioms primitive_fail
#print axioms primitive_div
#print axioms first_null
#print axioms null_keeps_allocated_storage
#print axioms stored_prefix
end R1Z.PV_RDB2D_CollectorCases
