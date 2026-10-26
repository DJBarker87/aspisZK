import F3T_Runtime
import F3T_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_FixtureRuntime
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3T_Runtime F3T_TwoPass

/-- A concrete observer of the canonical installed-source experiment. It
records the same execution, and does not postulate L159 as a new axiom. -/
def runtime {F C : Type} (c : Configuration F C) (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (P : ByteProver) : Runtime :=
  bind (OracleProgramRecording.record (annotatedWith D (F3T_Installed.source c hashv)
    (F3T_Canon.canon (lift c P)))) fun run=>.done (some run)

theorem evaluation {F C : Type} (c : Configuration F C) (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (P : ByteProver) (H : Bytes → State) :
    eval H (runtime c D hashv P)=
      ((eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P)))).1,
       some (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P))))) := by
  simp only [runtime,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

theorem binding {F C : Type} (c : Configuration F C) (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (P : ByteProver) :
    StoredCarrierBinding c D (F3T_Installed.source c hashv) P (runtime c D hashv P) := by
  intro H run observed accepted
  rw [evaluation] at observed
  exact (Option.some.inj observed).symm

theorem accepted {F C : Type} (c : Configuration F C) (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (sourceAccepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true) :
    ∃ run,(eval H (runtime c D hashv (.done s))).2=some run ∧ run.2.2=true := by
  refine ⟨eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c (.done s)))),?_,?_⟩
  · rw [evaluation]
  · rw [annotated_eval D _ (F3T_Installed.annotation c hashv),original_eval,
      F3T_Canon.canon_eval,lift_eval]
    change (eval H (F3T_Installed.source c hashv (F3T_Canon.canonInput (input c s)))).2=true
    rw [F3T_Installed.physical c hashv (F3T_Canon.canonInput (input c s)) (input c s) rfl rfl]
    exact sourceAccepted

#print axioms evaluation
#print axioms binding
#print axioms accepted
end AspisR1.F3X_FixtureRuntime
end
