import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PV_L2_F3SourceJoint

/-! Source-shaped counts at the exact endpoint field, honest builder and
owned decoder. The deployment's full native/L1/ROM-history join remains open. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_HeadlineF3
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds
  R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload R1Z.Batched R1Z.PredicateR1 R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.QueryScanRealLazyBound
  R1Z.PhaseProtocolInstanceBin R1Z.PremisesR1PBin R1Z.MaskImageVR1
attribute [local instance] Classical.propDecidable
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
attribute [local irreducible] PrivacyR1AcctBasis.basis
  ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P
variable {CommitHandle Aux : Type} (template : R1Wire K CommitHandle Aux)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
local notation "base" => PrivacyR1AcctModel.base template PhaseWireLog2Bin.log
local notation "h" => PhaseWireLog2Bin.honest PrivacyR1HeadlineDeployedReal.input
local notation "width" => List.length (R1Wire.pubBytes base x)
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base width h B outputs x)
local notation "seed" => PrivacyR1AcctModel.seed W PrivacyR1HeadlineDeployedReal.ownedDecode
  PhaseWireLog2Bin.fib PhaseWireLog2Bin.opens
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base width h B outputs x seed)
local notation "R" => RomFiniteBin.rom (baseWire base) (RomGrammarBin.bound width)
local notation "source" => ProverCommitReencode16.experiment W Pr 8
  PrivacyR1HeadlineWire2.eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
  ProverCommitReencode16.encode

theorem absorption_actual (w : (h).Instance) (ch : Challenges K)
    (hw : (h).public w = x.1)
    (hP : P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB ch)
    (hV : VR1 h ch w)
    (test : Option (View K CommitHandle Aux R1Bat × PV_L2_F3Tape.History) → ℚ) :
    mean (fun p : ProverCommitSourceDecoder.Inputs × Tape K F =>
      test ((PV_L2_F3SourceJoint.sourceObserved («K» := K) p.1).map (fun a =>
        (view h B outputs x w ch (ProverCommitTapeCompletion.complete a.1
          (ProverCommitTapeCompletion.padding p.2)),a.2)))) =
    mean (fun p : ProverCommitSourceDecoder.Inputs × Tape K F =>
      test ((PV_L2_F3SourceJoint.sourceObserved («K» := K) p.1).map (fun a =>
        (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x ch p.2,a.2)))) := by
  obtain ⟨hpub,hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
  simpa only [PV_L2_F3Absorption.sourceView,PV_L2_F3Absorption.simView,
    PV_L2_F3SourceJoint.source_observed] using
      PV_L2_F3Absorption.source_count_absorption h B outputs x w ch hB hpub hs hP hV hw test

#print axioms absorption_actual
end R1Z.PV_L2_HeadlineF3
