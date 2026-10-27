import RPz7_F3T_ByteTransport
import F3T_Probability
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Runtime
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried F3T_CanonicalJoin
open RawRecordedOracleExtractionMassBin
abbrev Runtime := Program Bytes State (Option F3T_Experiment.RunView)

def StoredCarrierBinding {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (runtime : Runtime) : Prop :=
  ∀ H run,(eval H runtime).2=some run → run.2.2=true →
    run=eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))

def runtimeMass (v : View Bytes State (Option F3T_Experiment.RunView)) : Rat :=
  match v.2 with | none=>0 | some run=>failureMass (view run)

def deployedFailure (runtime : Runtime) : Rat := lazyMean runtime emptyTable runtimeMass

theorem nonnegative (run : RawCutProverCompiler.RunView) : 0≤failureMass run :=
  OraclePortRuntimeBindingC7.failure_nonnegative run

theorem transport {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (runtime : Runtime)
    (binding : StoredCarrierBinding c D rust P runtime) :
    deployedFailure runtime≤lazyMean (projected D (F3T_Canon.canon (lift c P))) emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none=>exact nonnegative _
  | some run=>
    change failureMass (view run)≤failureMass (eval H (projected D (F3T_Canon.canon (lift c P))))
    by_cases ha : run.2.2=true
    · have same := binding H run hr ha
      have sourceAccepted : (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))).2.2=true := by
        rw [← same];exact ha
      rw [F3T_ByteTransport.annotated_eq c D rust physical raw _ (canon_lift_carried c P) H sourceAccepted] at same
      rw [same,projected_eval]
    · have zero : failureMass (view run)=0 := by
        unfold failureMass
        simp only [view] at *
        simp [ha,indicator,mean_const]
      rw [zero];exact nonnegative _

#print axioms nonnegative
#print axioms transport
end AspisR1.F3T_Runtime
end
