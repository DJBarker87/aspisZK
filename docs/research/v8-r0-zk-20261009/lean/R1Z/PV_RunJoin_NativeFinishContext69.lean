import R1Z.PV_RunJoin_NativeArithmeticImages69
import R1Z.PV_RunJoin_NativeFinishSemantic66
import R1Z.PV_RunJoin_NativeFinishClaim66
import R1Z.PV_RunJoin_NativeFinishStored63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinishContext69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_FinishContext (types base)
      (opsNative base heap box ops runtime world) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  intro phase prepared salts p hc hp hs hf coeff images
  have arithmetic := PV_RunJoin_NativeArithmeticImages69.complete base heap box ops runtime world
    phase prepared salts p hp hs hf hc images
  have context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase.val) p :=
    ⟨prepared,salts,hp,hs,hf⟩
  have semantic := PV_RunJoin_NativeFinishSemantic66.complete base heap box ops runtime world phase p context
  have claim := PV_RunJoin_NativeFinishClaim66.complete base heap box ops runtime world phase p context
  have stored := PV_RunJoin_NativeFinishStored63.complete base heap box ops runtime world phase.val p context
  exact ⟨arithmetic.1,arithmetic.2.1,arithmetic.2.2,semantic,claim,stored.1,stored.2⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeFinishContext69
