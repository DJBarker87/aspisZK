import RPz7_GExq_FirstSource
import RPz7_GExq_SecondSource
import RPz7_GExp_SecondPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_ChildCode
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- The only conditions needed at the two verifier call sites. They will be
proved from the containing caller's literal dictionary and release observer. -/
def Admissible (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    {A : Type} : S2W_Trace.Call A → Prop
  | .op10 D _ _ _ _ _ obs => (∀ h parts, D.digest h parts = hashv parts) ∧ obs = none
  | .op11 D _ _ _ _ obs => (∀ h parts, D.digest h parts = hashv parts) ∧ obs = none
  | _ => True

def execute {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    {A : Type} (call : S2W_Trace.Call A) : Code A :=
  let sdk := GExp_SecondPair.sdk adapter ops stage finish reserved query geo B std
  match call with
  | .op10 D semantic pub proof split hash _ => do
      let r ← GExq_FirstCode.code (GExp_FirstPair.base ops reserved query geo) B std hashv
        (AspisS6CurrentFirstInstallation.toDigest D)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash
      pure (SdkD_FirstChild.answer r)
  | .op11 D pub proof checkpoint hash _ =>
      GExq_SecondCode.code (GExp_SecondPair.base stage finish reserved query geo)
        reserved hashv D pub proof checkpoint hash
  | other => liftResult (S2W_Trace.invoke sdk other)

theorem erasure {F C A : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (call : S2W_Trace.Call A) (valid : Admissible hashv call) :
    erase (SdkC_Source.dictionary hashv) ()
      (execute adapter ops stage finish reserved query geo B std hashv call) =
      S2W_Trace.invoke (GExp_SecondPair.sdk adapter ops stage finish reserved query geo B std) call := by
  cases call <;> simp only [execute]
  all_goals try exact erase_lift _ _ _
  · obtain ⟨law,rfl⟩ := valid
    simp only [erase_bind,erase_pure]
    rw [GExq_FirstSource.source _ _ _ _ _ _ law]
    rw [GExp_FirstPair.installed]
    rfl
  · obtain ⟨law,rfl⟩ := valid
    rw [GExq_SecondSource.source _ _ _ _ _ (law _)]
    change VTop_Stages.verifier.candidate.tx2_authenticated
      (GExp_SecondCode.installed (GExp_SecondPair.base stage finish reserved query geo) reserved) _ _ _ _ _ _ = _
    rw [GExp_SecondPair.installed]
    rfl

#print axioms erasure
end AspisR1.GExq_ChildCode
end
