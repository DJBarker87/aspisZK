import SCE_SingleRuntime
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SourceFirst
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_Carried F3T_CanonicalJoin

/-- Accepted first-pass source-to-model transport uses the RETAINED raw join,
not a runtime binding. The source and model executions share P and H. -/
theorem original {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (H : Bytes → State)
    (accepted : (eval H (originalWith rust (F3T_Canon.canon (lift c P)))).2.2 = true) :
    eval H (originalWith rust (F3T_Canon.canon (lift c P))) =
      eval H (F3T_Experiment.original D (F3T_Canon.canon (lift c P))) := by
  have first : (eval H (rust (eval H (F3T_Canon.canon (lift c P))).2)).2 = true := by
    simpa only [F3T_TwoPass.original_eval] using accepted
  rw [F3T_TwoPass.original_eval,F3T_Experiment.original_eval,
    carried_join c D rust physical raw _ (canon_lift_carried c P H) H first]

#print axioms original
end AspisR1.SCE_SourceFirst
end
