import F3T_TwoPass
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AcceptedTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass

theorem original_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (join : RawJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (originalWith rust P)).2.2=true) :
    eval H (originalWith rust P)=eval H (original D P) := by
  rw [F3T_TwoPass.original_eval] at ha ⊢
  rw [F3T_Experiment.original_eval,join H _ ha]

theorem built_words (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (join : RawJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (originalWith rust P)).2.2=true) :
    build D (view (eval H (originalWith rust P)))=build D (view (eval H (original D P))) := by
  rw [original_eq D rust join P H ha]

theorem annotated_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (inv : AnnotationInvariant rust) (join : RawJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (annotatedWith D rust P)).2.2=true) :
    eval H (annotatedWith D rust P)=eval H (recorded D (build D) P) := by
  rw [F3T_TwoPass.annotated_eval D rust inv P H] at ha ⊢
  have first : (eval H (originalWith rust P)).2.2=true := ha
  have firstEq := original_eq D rust join P H first
  rw [firstEq,F3T_Experiment.recorded_eval]
  have accept : (eval H (rust (eval H (original D P)).2.1)).2=true := by
    rw [← firstEq,F3T_TwoPass.original_eval]
    exact first
  rw [join H _ accept]

#print axioms original_eq
#print axioms built_words
#print axioms annotated_eq
end AspisR1.F3T_AcceptedTransport
end
