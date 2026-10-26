import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SingleRuntime
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier

/-- Single source-pair execution recorded without an oracle replay. This is a
source-model runtime; association to adaptive account execution is separate. -/
def runtime {F C : Type} (c : DrvC_Installation.Configuration F C)
    (rust : Verifier) (P : ByteProver) : F3T_Runtime.Runtime :=
  bind (OracleProgramRecording.record (originalWith rust (F3T_Canon.canon (lift c P))))
    fun run => .done (some run)

theorem evaluation {F C : Type} (c : DrvC_Installation.Configuration F C)
    (rust : Verifier) (P : ByteProver) (H : Bytes → State) :
    eval H (runtime c rust P) =
      let v := eval H (originalWith rust (F3T_Canon.canon (lift c P)))
      (v.1,some v) := by
  simp only [runtime,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

#print axioms evaluation
end AspisR1.SCE_SingleRuntime
end
