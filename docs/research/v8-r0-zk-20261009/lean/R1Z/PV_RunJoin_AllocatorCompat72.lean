import R1Z.PV_RunJoin_NativeAllocatorSequence69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AllocatorCompat72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem success {T S F : Type} (base : ExternalTypes)
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (source threaded : PV_FXM_ReserveWorld.World S F) (v : alloc.vec.Vec T) (n : Usize)
    (hs : letI : ExternalTypes := types base
      (PV_RunJoin_AllocatorWorld63.execute runtime source v n).returned=.ok ())
    (ht : letI : ExternalTypes := types base
      (PV_RunJoin_AllocatorWorld63.execute runtime threaded v n).returned=.ok ()) :
    letI : ExternalTypes := types base
    PV_FXM_ReserveSelected.returned runtime.encode (PV_RunJoin_AllocatorWorld63.execute runtime source v n).returned=
      PV_FXM_ReserveSelected.returned runtime.encode (PV_RunJoin_AllocatorWorld63.execute runtime threaded v n).returned := by
  letI : ExternalTypes := types base
  rw [hs,ht]

#print axioms success
end R1Z.PV_RunJoin_AllocatorCompat72
