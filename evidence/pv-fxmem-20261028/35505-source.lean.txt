import R1Z.ProverRwFullExternalFuns
import R1Z.PV_FXM_DropWorld
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_DropSelected
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Only the type occurring at the single emitted op4 call is installed.
This definition deliberately retains the old callback at every other type. -/
def callback (ops : ExternalFuns) {T : Type} (x : T) : Result Unit :=
  by
    classical
    exact if T = alloc.vec.Vec U32 then .ok () else ops.op4 x

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op4 := callback ops}

theorem installed (ops : ExternalFuns) (v : alloc.vec.Vec U32) :
    @core.mem.drop _ (selected ops) _ v = .ok () := by
  change callback ops v = .ok ()
  simp only [callback,ite_true]

theorem other_types (ops : ExternalFuns) {T : Type}
    (h : T ≠ alloc.vec.Vec U32) (x : T) :
    (selected ops).op4 x = ops.op4 x := by
  change callback ops x = ops.op4 x
  simp only [callback,h,ite_false]

/-- Restoring op4 recovers the entire original record, not just a sample of
fields. Consequently every other callback is literally unchanged. -/
theorem other_fields (ops : ExternalFuns) :
    {selected ops with op4 := ops.op4} = ops := rfl

theorem projection {S F : Type} (ops : ExternalFuns)
    (v : alloc.vec.Vec U32) (free : Nat → Nat → Nat → S → S)
    (b : PV_FXM_DropWorld.Buffer) (w : PV_FXM_DropWorld.World S F) :
    Result.ok (PV_FXM_DropWorld.native free b w).1 =
      @core.mem.drop _ (selected ops) _ v := by
  rw [installed]

/-- The complete execution retains the world effect before running the caller.
The value projection alone is not the execution-composition theorem. -/
theorem execution {S F A : Type} (ops : ExternalFuns)
    (v : alloc.vec.Vec U32) (free : Nat → Nat → Nat → S → S)
    (b : PV_FXM_DropWorld.Buffer) (w : PV_FXM_DropWorld.World S F)
    (caller : Unit → PV_FXM_DropWorld.World S F → Result A) :
    (do let u ← @core.mem.drop _ (selected ops) _ v
        caller u (PV_FXM_DropWorld.release free b w)) =
      caller (PV_FXM_DropWorld.native free b w).1
        (PV_FXM_DropWorld.native free b w).2 := by
  rw [installed]
  rfl

#print axioms installed
#print axioms other_types
#print axioms other_fields
#print axioms projection
#print axioms execution
end R1Z.PV_FXM_DropSelected
