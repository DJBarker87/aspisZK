import R1Z.PV_RunJoin_ExtraTotal69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeExtraTotal69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem arithmetic {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @PV_RunJoin_ExtraTotal69.Arithmetic (types base) (opsNative base heap box ops runtime world) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  refine ⟨PV_RunJoin_NativeQuarticTotal69.add base heap box ops runtime world,
    PV_RunJoin_NativeQuarticTotal69.mul base heap box ops runtime world,?_⟩
  exact ⟨_,PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world⟩

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (coefficients : Array aspis_core.field.QM31 1024#usize) (a b : aspis_core.field.QM31) :
    ∃ out,@host_semantic.extra (types base) (opsNative base heap box ops runtime world) coefficients a b=ok out :=
  @PV_RunJoin_ExtraTotal69.complete (types base) (opsNative base heap box ops runtime world)
    (arithmetic base heap box ops runtime world) coefficients a b

#print axioms arithmetic
#print axioms complete
end R1Z.PV_RunJoin_NativeExtraTotal69
