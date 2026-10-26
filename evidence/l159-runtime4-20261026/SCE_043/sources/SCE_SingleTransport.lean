import SCE_SingleAnnotation
import SCE_FailureZero
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SingleTransport
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin
open RawRecordedOracleExtractionMassBin

theorem failure_le {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) :
    F3T_Runtime.deployedFailure (SCE_SingleRuntime.runtime c rust P) ≤
      lazyMean (F3T_Charged.projected D (F3T_Canon.canon (lift c P))) emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  rw [SCE_SingleRuntime.evaluation]
  change failureMass (view (eval H (originalWith rust (F3T_Canon.canon (lift c P))))) ≤ _
  by_cases accepted : (eval H (originalWith rust (F3T_Canon.canon (lift c P)))).2.2 = true
  · rw [SCE_SingleAnnotation.mass c D rust physical raw P H accepted]
    have annotatedAccepted : (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))).2.2 = true := by
      rw [F3T_TwoPass.annotated_eval D rust (fun _ _ => physical _ _ rfl rfl)]
      exact accepted
    rw [F3T_ByteTransport.annotated_eq c D rust physical raw _
      (F3T_Carried.canon_lift_carried c P) H annotatedAccepted,F3T_Charged.projected_eval]
  · rw [SCE_FailureZero.rejected _ accepted]
    exact F3T_Runtime.nonnegative _

#print axioms failure_le
end AspisR1.SCE_SingleTransport
end
