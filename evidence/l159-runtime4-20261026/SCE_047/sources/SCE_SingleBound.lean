import SCE_SingleTransport
import F3T_RuntimeBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SingleBound
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin

/-- Single source-pair runtime bound WITHOUT StoredCarrierBinding. This is a
source-model theorem. Applying it to SCE_Experiment.runtime still requires
account/source event transport; that obligation is not an input here. -/
theorem source_failure_bound {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    F3T_RuntimeBound.failureModel (SCE_SingleRuntime.runtime c rust P) ≤ StartChargeNumeric.totalBound Q := by
  have lifted : ∀ H : Bytes → State, (eval H (lift c P)).1.length ≤ Q := by
    intro H
    rw [lift_eval]
    exact queries H
  have bound := F3T_Probability.failure_bound D (lift c P) Q lifted
  have transport := SCE_SingleTransport.failure_le c D rust physical raw P
  apply (add_le_add (transport.trans bound) QueryScanModelFailure.exhaustion_bound).trans_eq
  unfold StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
  ring

#print axioms source_failure_bound
end AspisR1.SCE_SingleBound
end
