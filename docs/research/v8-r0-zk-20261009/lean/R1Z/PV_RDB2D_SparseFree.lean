import R1Z.PV_RDB2D_SparseLayout
namespace R1Z.PV_RDB2D_SparseFree
open Aeneas Aeneas.Std Result PV_RDB2D_CollectorTrace
set_option autoImplicit false

def release {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (address capacity : Nat) (state : State S F) : Result (State S F) := do
  let s ← deallocate address (24*capacity) 8 state.resource.allocator
  ok {state with
    resource := {state.resource with
      allocator := s
      deallocCalls := state.resource.deallocCalls+1
      live := fun a => if a=address then false else state.resource.live a}
    trace := state.trace++[.deallocate (24*capacity) 8]
    initialized := fun a => if a=address then none else state.initialized a}

theorem layout {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (address capacity : Nat) (state : State S F) (s : S)
    (h : deallocate address (24*capacity) 8 state.resource.allocator=ok s) :
    (do let after ← release deallocate address capacity state; ok after.trace)=
      ok (state.trace++[.deallocate (24*capacity) 8]) := by
  simp only [release,h,bind_tc_ok]

#print axioms layout
end R1Z.PV_RDB2D_SparseFree
