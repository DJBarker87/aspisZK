import R1Z.PV_AL_MoveWorld
import R1Z.ProverRwFullFuns
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_MoveSelected
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

/-- The selected callback is the move reference, with no Copy/Clone bound. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op33 := fun _ v => PV_AL_RemoveModel.pop_move_reference v}

theorem callback {T : Type} (ops : ExternalFuns) (A : Type) (v : alloc.vec.Vec T) :
    (selected ops).op33 A v=PV_CBL_VectorPopSpec.reference v :=
  PV_AL_MoveLast.source v

theorem consumed {T : Type} (ops : ExternalFuns) (A : Type) (v : alloc.vec.Vec T) :
    @alloc.vec.Vec.pop _ (selected ops) T A v=
      ok (v.val.getLast?,(PV_CBL_VectorPopSpec.pop v).2) :=
  PV_AL_MoveLast.source v

/-- Complete value callback is the projection of the native world execution. -/
theorem native_projection {T F : Type} (ops : ExternalFuns) (A : Type)
    (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World)
    (memory : PV_AL_MoveMemory.Memory) (frame : F) :
    (do let o ← PV_AL_MoveWorld.nativeWorld b w memory frame;
        ok (o.returned,o.remaining))=(selected ops).op33 A b.value := by
  rw [PV_AL_MoveWorld.native_complete,callback]
  rfl

/-- World equality includes allocation counters/history, buffer, capacity,
data memory and an arbitrary external frame, before callback projection. -/
theorem native_reference {T F : Type} (b : PV_AL_PopWorld.Buffer T)
    (w : PV_AL_PopWorld.World) (memory : PV_AL_MoveMemory.Memory) (frame : F)
    (width : Nat) :
    PV_AL_MoveWorld.nativeWorld b w memory frame=
      PV_AL_MoveWorld.referenceWorld b w memory frame width :=
  PV_AL_MoveWorld.source_reference b w memory frame width

#print axioms selected
#print axioms callback
#print axioms consumed
#print axioms native_projection
#print axioms native_reference
end R1Z.PV_AL_MoveSelected
