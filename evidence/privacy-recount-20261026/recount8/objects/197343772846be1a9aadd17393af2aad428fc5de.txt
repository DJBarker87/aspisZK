import R1Z.PV_RDB2C_PV_RDB1_V181
import R1Z.PV_RDB2C_V258
import R1Z.PV_RDB2C_V259
namespace R1Z.PV_RDB2C_ResourceInstance
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld

def empty (T : Type) (address : Nat) : Buffer T := ⟨address,0,[],by rfl⟩

/-- Every layout/overflow guard precedes allocation. On the fixed 1024-element
WideExact buffer they pass under the target's public size bounds. -/
theorem materialize_request {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (width : shape.width=32)
    (wordBound : 1024≤wordMax) (byteBound : 32768≤byteMax)
    (address : Nat) (world : World S F) :
    native step wordMax byteMax shape (empty T address) 1024 world =
      finish step shape (empty T address) 1024 world := by
  have hw : ¬1024>wordMax := by omega
  have hb : ¬32768>byteMax := by omega
  simp only [native,growExact,empty,List.length_nil,Nat.sub_self,
    Nat.zero_add,width,show (1024:Nat)>0 by omega,show ¬(32=0) by omega,
    hw,show (1024:Nat)*32=32768 by rfl,hb,ite_true,ite_false]

/-- Native allocation failures retain the private allocator post-state, the
unchanged buffer and every initialized allocation. No successful-allocation
premise is imposed on the fixed public request. -/
theorem failed_request {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (world : World S F) (state : S)
    (h : step ⟨address,0,1024,shape⟩ world.allocator=(none,state)) :
    (finish step shape (empty T address) 1024 world).buffer=empty T address ∧
    (finish step shape (empty T address) 1024 world).world.allocator=state ∧
    (finish step shape (empty T address) 1024 world).world.memory=world.memory ∧
    (finish step shape (empty T address) 1024 world).world.live=world.live := by
  have hh := allocation_error step shape (empty T address) 1024 world state h
  exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

theorem request_no_reallocation {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (shape : Shape) (address : Nat) (state : S) :
    PV_RDB1_V183_ReservePrimitive.step allocate reallocate ⟨address,0,1024,shape⟩ state =
      allocate (PV_RDB1_V183_ReservePrimitive.layout shape 1024) state :=
  PV_RDB1_V183_ReservePrimitive.allocate_branch allocate reallocate _ state rfl

/-- Complete reserve/reference equality is inherited with allocation failure,
reallocation prefix and private world effects, not a returning-value-only law. -/
theorem reserve_complete {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (buffer : Buffer T)
    (additional : Nat) (world : World S F) :
    native step wordMax byteMax shape buffer additional world=
      reference step wordMax byteMax shape buffer additional world :=
  PV_RDB1_V183.complete step wordMax byteMax shape buffer additional world

theorem selected_layouts_padded : (32:Nat)%4=0 ∧ (2116:Nat)%4=0 := by decide

#print axioms selected_layouts_padded
#print axioms materialize_request
#print axioms failed_request
#print axioms request_no_reallocation
#print axioms reserve_complete
end R1Z.PV_RDB2C_ResourceInstance
