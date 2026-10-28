import R1Z.PV_RunJoin_WeightMutation47
import R1Z.PV_RunJoin_WeightArray46
import R1Z.ProverCommitWeightsMaterialBinding53
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightMaterialLoop47
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (toWide)
open PV_RunJoin_WeightCellSource47 (Powers powerArray)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)

theorem copied (w : W) (hs : w.variant=.S2) (k : Powers) :
    AspisR1ProducerRelease47.weights_material53.all (state w) (amap toWide (powerArray k))=
      mapResult (amap toWide) (PV_B2_F_MutationModel.remaining w k 1024 0#usize
        PV_B2_F_AllocationTransport.zeros) := by
  unfold AspisR1ProducerRelease47.weights_material53.all
  rw [PV_RunJoin_WeightCellIndices46.zero,←PV_RunJoin_WeightArray46.replicate]
  rw [PV_RunJoin_WeightFill46.complete w hs _ 1024 _ _ 1024#u16 rfl]
  rw [PV_RunJoin_WeightMutation47.remaining w hs k 1024 _ 0#usize (by decide)
    PV_B2_F_AllocationTransport.zero_suffix]
#print axioms copied

theorem original (w : W) (hs : w.variant=.S2) (k : Powers) :
    AspisR1ProducerRelease47.weights_material53.all (state w) (amap toWide (powerArray k))=
      mapResult (amap toWide) (PV_B2_F_MaterializeFrozen.remaining w k 1024 0#usize
        PV_B2_F_AllocationTransport.zeros) := by
  rw [copied w hs]
  have h := PV_B2_F_OriginalMutation.loop w k PV_B2_F_AllocationTransport.zeros
    0#usize PV_B2_F_AllocationTransport.zero_suffix
  change PV_B2_F_OriginalMutation.remaining w k 1024 0#usize _=
    PV_B2_F_MutationModel.remaining w k 1024 0#usize _ at h
  rw [←h,PV_B2_F_MaterializeFrozen.loops]
#print axioms original
end R1Z.PV_RunJoin_WeightMaterialLoop47
