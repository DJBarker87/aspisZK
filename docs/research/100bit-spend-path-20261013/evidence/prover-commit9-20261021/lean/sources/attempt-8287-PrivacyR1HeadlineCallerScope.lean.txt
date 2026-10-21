import R1Z.PrivacyR1HeadlineV2
import R1Z.ProverCommitCallerObstruction
/-! D112 retains an arbitrary decoder. This module checks that exact
headline interface before any proposed deletion of CallerLaw. It does not
assert an execution certificate for the shipped prover. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineCallerScope
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)

local notation "log" => PhaseWireLog2Bin.log
local notation "base" => PrivacyR1AcctModel.base template log
variable (input : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
variable (decode : (Fin PrivacyR1AcctModel.E₁ → OracleAnswer) →
    (Fin PrivacyR1AcctModel.E₂ → OracleAnswer) → Option (Tape K F))

local notation "fib" => PhaseWireLog2Bin.fib
local notation "opens" => PhaseWireLog2Bin.opens
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
open R1Z.PrivacyR1HeadlineWire2
local notation "source" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
theorem tapeOf_eq_decode :
    (R1Z.PhaseLocalityBin.R1PhaseProver.toProver
      (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)).tapeOf = decode := rfl

theorem failed_decode_not_caller
    (failed : ∀ e₁ e₂, decode e₁ e₂ = none) :
    ¬ ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver
        (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) := by
  apply ProverCommitCallerObstruction.all_failure_not_law
  exact failed

/-- An unconditional counterexample at the exact D112 constructor, with the
same source block counts and all its constructed address/opening data. -/
theorem all_none_decode_not_caller :
    ¬ ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver
        (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x
          (PrivacyR1AcctModel.seed
            (R1Z.PhaseLocalityBin.R1PhaseWire.toWire
              (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
            (fun _ _ => none) fib opens))) := by
  exact failed_decode_not_caller template input outputs x (fun _ _ => none) (fun _ _ => rfl)

#print axioms all_none_decode_not_caller
#print axioms tapeOf_eq_decode
#print axioms failed_decode_not_caller
end R1Z.PrivacyR1HeadlineCallerScope
