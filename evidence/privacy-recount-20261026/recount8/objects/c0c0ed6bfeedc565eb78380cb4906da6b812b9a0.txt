import R1Z.PV_AL_MoveSelected
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_MoveClosure
open ProverRwFull
set_option autoImplicit false

/-- Complete selected callback and both source-library executions share the
same observation. No source-equality or allocation-effect premise is assumed. -/
theorem complete [ExternalTypes] {T F : Type} (ops : ExternalFuns) (A : Type)
    (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : PV_AL_MoveMemory.Memory) (frame : F) (width : Nat) :
    ∃ o : PV_AL_MoveMemory.Observation T F,
      PV_AL_MoveWorld.nativeWorld b w memory frame=ok o ∧
      PV_AL_MoveWorld.referenceWorld b w memory frame width=ok o ∧
      @alloc.vec.Vec.pop _ (PV_AL_MoveSelected.selected ops) T A b.value=
        ok (o.returned,o.remaining) ∧
      o.returned=b.value.val.getLast? ∧ o.remaining.val=b.value.val.dropLast ∧
      o.buffer=b.address ∧ o.capacity=b.capacity ∧ o.world=w ∧
      o.memory=memory ∧ o.frame=frame := by
  refine ⟨PV_AL_MoveWorld.expected b w memory frame,
    PV_AL_MoveWorld.native_complete b w memory frame,
    PV_AL_MoveWorld.reference_complete b w memory frame width,?_,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  exact PV_AL_MoveSelected.consumed ops A b.value

/-- Arbitrary initial counters/history are retained; no allocation, reallocation
or deallocation increment is hidden by the value projection. -/
theorem allocation_delta {T F : Type} (b : PV_AL_PopWorld.Buffer T)
    (w : PV_AL_PopWorld.World) (memory : PV_AL_MoveMemory.Memory) (frame : F) :
    ∃ o, PV_AL_MoveWorld.nativeWorld b w memory frame=ok o ∧
      o.world.alloc-w.alloc=0 ∧ o.world.realloc-w.realloc=0 ∧
      o.world.dealloc-w.dealloc=0 ∧ o.world.history=w.history := by
  refine ⟨PV_AL_MoveWorld.expected b w memory frame,
    PV_AL_MoveWorld.native_complete b w memory frame,?_,?_,?_,rfl⟩
  all_goals exact Nat.sub_self _

/-- Every representable generic vector admits the full world carrier. -/
theorem nonvacuous {T : Type} (v : alloc.vec.Vec T) (address : Nat) :
    ∃ b : PV_AL_PopWorld.Buffer T, b.value=v ∧ b.address=address ∧
      b.capacity=v.val.length :=
  ⟨⟨address,v.val.length,v,le_refl _⟩,rfl,rfl,rfl⟩

#print axioms complete
#print axioms allocation_delta
#print axioms nonvacuous
end R1Z.PV_AL_MoveClosure
