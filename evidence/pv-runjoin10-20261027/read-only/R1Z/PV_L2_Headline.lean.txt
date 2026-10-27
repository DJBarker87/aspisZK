import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PV_L2_F5Absorption

/-! Specialization to the EXACT W, Pr, owned decoder, eight attempts and
reencoded source of privacy_headline_deployed. This removes RAddrIn/RCausal
and builder premises from the local F5 model bridges using existing proofs.
It does not remove RustRealRefinement or the native L1/L2 deployment joins. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_Headline
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

theorem deployed_parser : (W).dec = PhaseSamplerParserBin.decode := rfl

theorem deployed_source_carrier : (source).RealRand = ((W).Tab × (Fin 8 → SecP)) := rfl

/-- Real-to-lazy only. The existing honest-read collision event is unchanged. -/
theorem real_to_lazy_actual (w : (h).Instance) (s : Fin 8 → AttS W Pr)
    (hn : ¬ lazyBad W Pr R 8 PrivacyR1HeadlineWire2.eight_pos h B outputs x w s) :
    PV_L2_F5Transport.vectorHistory W Pr 8
      (realVector W Pr 8 h B outputs x w
        (toRP W Pr R h B outputs x w PrivacyR1HeadlineWire2.eight_pos s)) =
      (fun k => PV_L2_F5.history (fun j => (s k).2.1 (.inl (.qb j)))) := by
  have cov := PhaseProtocolCoverageBin.read_coverage base width h B outputs x seed (le_refl _)
  have hin : RAddrIn W Pr R h B outputs x w :=
    RomGrammarBin.address_domain (baseWire base) width Pr h B outputs x cov w
  have hc : RCausal W Pr h B outputs x w :=
    (causal_iff W Pr h B outputs x w).mpr
      (causal_premise base width h B outputs x seed w)
  exact PV_L2_F5Transport.real_to_lazy W Pr R 8 PrivacyR1HeadlineWire2.eight_pos
    h B outputs x w hin hc s hn

/-- Fixed-coins simE leg using the endpoint's actual admitted builder proof.
It carries ALL eight parser histories, including rejected attempts. The
P_R1/VR1 guards have the same meaning as in the existing absorption theorem. -/
theorem absorption_actual (coins : Fin 8 → R1Coins (W).Cm (W).Tab) (k : Fin 8)
    (w : (h).Instance) (hw : (h).public w = x.1)
    (hP : P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB (drawW W (coins k)))
    (hV : VR1 h (drawW W (coins k)) w)
    (test : ((Fin 8 → _) × View K CommitHandle Aux R1Bat) → ℚ) :
    mean (fun t : Tape K F => test
      ((fun j => PV_L2_F5Transport.coinHistory W (coins j)),
        view h B outputs x w (drawW W (coins k)) t)) =
    mean (fun t : Tape K F => test
      ((fun j => PV_L2_F5Transport.coinHistory W (coins j)),
        simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x (drawW W (coins k)) t)) := by
  obtain ⟨hpub,hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
  exact PV_L2_F5Absorption.fixed_coins_joint W h B hB outputs x hpub hs
    8 coins k w hP hV hw test

#print axioms deployed_parser
#print axioms deployed_source_carrier
#print axioms real_to_lazy_actual
#print axioms absorption_actual
end R1Z.PV_L2_Headline
