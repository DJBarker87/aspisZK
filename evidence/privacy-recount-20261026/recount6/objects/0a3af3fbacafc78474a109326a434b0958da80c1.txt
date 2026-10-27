import R1Z.PV_AL_MoveMemory
import R1Z.PV_AL_MoveNativeValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_MoveWorld
open PV_AL_MoveMemory
set_option autoImplicit false

def expected {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) : Observation T F :=
  ⟨(PV_CBL_VectorPopSpec.pop b.value).1,(PV_CBL_VectorPopSpec.pop b.value).2,
    b.address,b.capacity,w,memory,frame⟩

/-- Raw remove(last)'s snapshot-copy step, including size-zero elements. -/
def referenceMemory {T : Type} (b : PV_AL_PopWorld.Buffer T) (memory : Memory)
    (width : Nat) : Memory :=
  let n := b.value.val.length
  if n=0 then memory else
    copyBytes memory (b.address+n*width) (b.address+(n-1)*width) ((n-(n-1)-1)*width)

theorem reference_memory {T : Type} (b : PV_AL_PopWorld.Buffer T) (memory : Memory)
    (width : Nat) : referenceMemory b memory width=memory := by
  by_cases hn : b.value.val.length=0
  · simp only [referenceMemory,hn,if_true]
  · simp only [referenceMemory,hn,if_false]
    exact last_copy memory b.address _ width (by omega)

/-- The allocation world, data-buffer bytes and arbitrary external frame are
carried explicitly. Native pop has read/header effects and no allocator call. -/
def nativeWorld {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) : Result (Observation T F) := do
  let (returned,remaining) ← PV_AL_MoveNativeValue.nativeValue b.value b.capacity
  ok ⟨returned,remaining,b.address,b.capacity,w,memory,frame⟩

/-- Safe move reference with its raw zero-length copy effect, not an assumed
world equation or an allocation-erased projection. -/
def referenceWorld {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) (width : Nat) : Result (Observation T F) := do
  let (returned,remaining) ← PV_AL_RemoveModel.pop_move_reference b.value
  ok ⟨returned,remaining,b.address,b.capacity,w,referenceMemory b memory width,frame⟩

theorem native_complete {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) : nativeWorld b w memory frame=ok (expected b w memory frame) := by
  simp only [nativeWorld,PV_AL_MoveNativeValue.source b.value b.capacity b.fits,
    PV_CBL_VectorPopSpec.reference,bind_tc_ok]
  rfl

theorem reference_complete {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) (width : Nat) :
    referenceWorld b w memory frame width=ok (expected b w memory frame) := by
  simp only [referenceWorld,PV_AL_MoveLast.source,PV_CBL_VectorPopSpec.reference,bind_tc_ok,
    reference_memory b memory width]
  rfl

theorem source_reference {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) (width : Nat) :
    nativeWorld b w memory frame=referenceWorld b w memory frame width := by
  rw [native_complete,reference_complete]

theorem checked_observation {T F : Type} (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : Memory) (frame : F) :
    ∃ o, nativeWorld b w memory frame=ok o ∧
      o.returned=b.value.val.getLast? ∧ o.remaining.val=b.value.val.dropLast ∧
      o.buffer=b.address ∧ o.capacity=b.capacity ∧ o.world=w ∧ o.memory=memory ∧ o.frame=frame :=
  ⟨expected b w memory frame,native_complete b w memory frame,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms expected
#print axioms referenceMemory
#print axioms reference_memory
#print axioms nativeWorld
#print axioms referenceWorld
#print axioms native_complete
#print axioms reference_complete
#print axioms source_reference
#print axioms checked_observation
end R1Z.PV_AL_MoveWorld
