import RPz7_F3T_Runtime
import F3T_ModelClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_RuntimeBound
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin F3T_Runtime

def failureModel (runtime : Runtime) : Rat :=
  deployedFailure runtime+QueryScanModelFailure.failureProbability (2^18)

theorem failure_bound {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q) (runtime : Runtime)
    (binding : StoredCarrierBinding c D rust P runtime) :
    failureModel runtime≤StartChargeNumeric.totalBound Q := by
  have lifted : ∀ H : Bytes → State,(eval H (lift c P)).1.length≤Q := by
    intro H;rw [lift_eval];exact queries H
  have b := F3T_Probability.failure_bound D (lift c P) Q lifted
  have t := F3T_Runtime.transport c D rust physical raw P runtime binding
  apply (add_le_add (t.trans b) QueryScanModelFailure.exhaustion_bound).trans_eq
  unfold StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
  ring

#print axioms failure_bound
end AspisR1.F3T_RuntimeBound
end
