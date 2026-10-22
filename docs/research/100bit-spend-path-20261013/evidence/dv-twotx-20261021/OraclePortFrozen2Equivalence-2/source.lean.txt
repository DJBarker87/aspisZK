import OraclePortFrozen2Decision
import OraclePortStoredAdmissionC4

/-! Lift Boolean equivalence to the same complete submitted proof, public
statement, stored bytes and oracle. Issued-log equality is not asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozen2
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4

theorem verifier_acceptance_eq (D : LiteralByteProtocol.Decoder) (i : Input) (H : Bytes → State) :
    (eval H (verifier D dV_frozen2 i)).2 =
      (eval H (verifier D OraclePortFrozenOrder.dV_frozen i)).2 := by
  unfold OraclePortStoredExperimentC4.verifier OraclePortExperiment.verifier
  rw [OracleDecisionFeasibilityBudget.verifier_eval,OracleDecisionFeasibilityBudget.verifier_eval]
  exact acceptance_eq H _ _ _

theorem original_acceptance_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (original D dV_frozen2 P)).2.2 =
      (eval H (original D OraclePortFrozenOrder.dV_frozen P)).2.2 := by
  simp only [original_eval]
  exact verifier_acceptance_eq D _ H

theorem annotated_acceptance_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (annotated D dV_frozen2 P)).2.2 =
      (eval H (annotated D OraclePortFrozenOrder.dV_frozen P)).2.2 := by
  unfold annotated
  simp only [recorded_eval]
  exact original_acceptance_eq D P H

#print axioms verifier_acceptance_eq
#print axioms original_acceptance_eq
#print axioms annotated_acceptance_eq
end AspisR1.OraclePortFrozen2
end
