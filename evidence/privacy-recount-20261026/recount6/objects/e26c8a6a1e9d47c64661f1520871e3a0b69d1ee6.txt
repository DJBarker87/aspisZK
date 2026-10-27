import R1Z.PV_AL_PopWorld
import R1Z.ProverRwFullFuns
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_PopSelected
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

/-- Candidate dictionary installation; native remove fidelity is audited separately. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op33 := fun _ v => PV_CBL_VectorPopSpec.reference v}

theorem callback {T : Type} (ops : ExternalFuns) (A : Type) (v : alloc.vec.Vec T) :
    (selected ops).op33 A v=ok (PV_CBL_VectorPopSpec.pop v) := rfl

theorem consumed {T : Type} (ops : ExternalFuns) (A : Type) (v : alloc.vec.Vec T) :
    @alloc.vec.Vec.pop _ (selected ops) T A v=
      ok (v.val.getLast?,(PV_CBL_VectorPopSpec.pop v).2) := rfl

/-- World carrier projects to the exact complete callback result. -/
theorem world_projection {T : Type} (ops : ExternalFuns) (A : Type)
    (b : PV_AL_PopWorld.Buffer T) (w : PV_AL_PopWorld.World) :
    (do let (r,b',_) ← PV_AL_PopWorld.reference b w; ok (r,b'.value)) =
      (selected ops).op33 A b.value := rfl

#print axioms selected
#print axioms callback
#print axioms consumed
#print axioms world_projection
end R1Z.PV_AL_PopSelected
