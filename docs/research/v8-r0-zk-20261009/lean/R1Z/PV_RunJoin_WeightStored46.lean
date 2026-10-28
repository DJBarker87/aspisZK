import R1Z.PV_RunJoin_WeightKernel46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightStored46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (Weight toWeight to251Variant amap)

def kernelState (w : Weight) : ProverCommitWeightsStorage53.State :=
  (PV_RunJoin_WeightCarrier46.tag (to251Variant w.variant),
   amap (amap (amap PV_RunJoin_WeightKernel46.toQ)) w.factors,
   amap (amap PV_RunJoin_WeightKernel46.toQ) w.points,
   amap PV_RunJoin_WeightKernel46.toQ w.extra)

theorem complete (w : Weight) :
    PV_RunJoin_WeightCarrier46.state (toWeight w)=kernelState w := by
  simp only [PV_RunJoin_WeightCarrier46.state,toWeight,kernelState,
    PV_RunJoin_WeightArray46.comp] <;> rfl

#print axioms complete
end R1Z.PV_RunJoin_WeightStored46
