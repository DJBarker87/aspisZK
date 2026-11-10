-- PCVU_ headline seed: which of the free stage dictionaries (reserved, query, geo, base, finish) of deployed_tx2_common are fixed at NNH_HostCtx.
-- Restatement only (definitional unfolding of the headline configuration); nothing here proves a frozen-source relation.
import Aeneas
import PRVEq_Tx2Frozen_s2
import NNH_HostCtx
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVU_Head
open AspisR1 VTop_Stages VTop_Stages.PRVFresh_VTop_l1 PCVN_Tx2Deployed

theorem constants_eq : NHT_Tx2CommonModel.constants = PCVN_Tx2Deployed.constants := by
  first | with_unfolding_all rfl | (funext ops; with_unfolding_all rfl)

theorem stage_eq (base : VTop_Stages.Ops) :
    NNH_Tx2SourceConfiguration.stage base = stageNNH NJC_ClosedCalls.inactive NHV_ReleaseOps.mark base := by
  unfold NNH_Tx2SourceConfiguration.stage stageNNH
  rw [constants_eq]

theorem stageBase_headline {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).stageBase =
      stageNNH NJC_ClosedCalls.inactive NHV_ReleaseOps.mark NNH_HostSeed.m0.stageBase := by
  rw [← stage_eq]
  with_unfolding_all rfl

theorem query_headline {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).query = NJJ_QueryOps.concrete := by
  with_unfolding_all rfl

theorem geometry_headline {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).geometry = NFN_NEW_GeometryDictionary.adopted := by
  with_unfolding_all rfl

theorem reserved_headline {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).reserved = (NNH_HostCtx.envOf c).reservation := by
  with_unfolding_all rfl

theorem headline_stage {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    DrvC_Installation.stage (NNH_HostCtx.configuration c) =
      Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark (NNH_HostCtx.configuration c).reserved
        (NNH_HostCtx.configuration c).query (NNH_HostCtx.configuration c).geometry
        NNH_HostSeed.m0.stageBase (NNH_HostCtx.configuration c).finish := by
  unfold DrvC_Installation.stage Dep
  rw [stageBase_headline]

theorem headline_tx2_common {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx)
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_common
        (xdep (PCVU_Tx2Frozen.yFrozen (NNH_HostCtx.configuration c).reserved
          (DrvC_Installation.stage (NNH_HostCtx.configuration c)))
          (DrvC_Installation.stage (NNH_HostCtx.configuration c)))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_common (DrvC_Installation.stage (NNH_HostCtx.configuration c))
        inst public_bytes proof checkpoint hash obs := by
  rw [headline_stage c]
  exact PCVU_Tx2Frozen.deployed_tx2_common_t (NNH_HostCtx.configuration c).reserved
    (NNH_HostCtx.configuration c).query (NNH_HostCtx.configuration c).geometry NNH_HostSeed.m0.stageBase
    (NNH_HostCtx.configuration c).finish inst public_bytes proof checkpoint hash obs

#print axioms constants_eq
#print axioms stage_eq
#print axioms stageBase_headline
#print axioms query_headline
#print axioms geometry_headline
#print axioms reserved_headline
#print axioms headline_stage
#print axioms headline_tx2_common
end PCVU_Head
