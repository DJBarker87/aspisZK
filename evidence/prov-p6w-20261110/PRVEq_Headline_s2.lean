-- PCVU_ headline seed: which of the free stage dictionaries (reserved, query, geo, base, finish) of deployed_tx2_common are fixed at NNH_HostCtx.
-- Restatement only (definitional unfolding of the headline configuration); nothing here proves a frozen-source relation.
-- s2 keeps the four theorems that compiled in s1 (L024); the stageBase and geometry equalities failed in s1 (rfl) and are not claimed.
import Aeneas
import PRVEq_Tx2Deployed_s1
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

theorem query_headline {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).query = NJJ_QueryOps.concrete := by
  with_unfolding_all rfl

theorem reserved_headline {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NNH_HostCtx.configuration c).reserved = (NNH_HostCtx.envOf c).reservation := by
  with_unfolding_all rfl

#print axioms constants_eq
#print axioms stage_eq
#print axioms query_headline
#print axioms reserved_headline
end PCVU_Head
