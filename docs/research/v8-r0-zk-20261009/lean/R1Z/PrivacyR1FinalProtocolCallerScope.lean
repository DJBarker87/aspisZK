import R1Z.PrivacyR1FinalProtocolCaller
import R1Z.ProverCommitCallerObstruction
import R1Z.ProverCommitReferenceReads
import R1Z.ProverCommitFoldSteps

/-! Exact scope audit on the existing caller endpoint. The protocol constructs
its leaf/grammar/order data but still inherits tapeOf from the supplied seed.
Consequently the new extracted step results cannot delete CallerLaw without
an actual source-to-tapeOf transport. No endpoint premise is weakened. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1FinalProtocolCallerScope
open R0P R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.GamesR1PBin
open R1Z.PhaseProtocolInstanceBin
local notation "K" => AspisWideTower.WideExact
local notation "F" => @R1Z.ProverCommitWordCarrier.sourceBase K inferInstance inferInstance
variable {CommitHandle Aux : Type}
variable (base : R1Wire K CommitHandle Aux) (publicWidth : Nat)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)

theorem tapeOf_inherited
    (seed : R1ProverP K CommitHandle Aux F
      (wire base publicWidth h B outputs x).toWire) :
    (prover base publicWidth h B outputs x seed).toProver.tapeOf = seed.tapeOf := rfl

theorem caller_not_automatic
    (seed : R1ProverP K CommitHandle Aux F
      (wire base publicWidth h B outputs x).toWire) :
    ¬ R1Z.ProverCommitCallerInstance.CallerLaw
      (prover base publicWidth h B outputs x
        (R1Z.ProverCommitCallerObstruction.failedCaller seed)).toProver := by
  apply R1Z.ProverCommitCallerObstruction.all_failure_not_law
  intro _ _
  rfl

#print axioms tapeOf_inherited
#print axioms caller_not_automatic
#print axioms R1Z.PrivacyR1FinalProtocolCaller.privacy_R1_protocol_caller
end R1Z.PrivacyR1FinalProtocolCallerScope
