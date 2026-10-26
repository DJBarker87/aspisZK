import F3U_CollisionJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_TwoPass
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried
open F3U_CollisionJoin

theorem annotated_or_collision {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : F3T_CanonicalJoin.Physical rust)
    (bad : Exception) (join : Join c D rust bad) (P : Prover)
    (carrier : ∀ H,Carried c (eval H P).2) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D rust P)).2.2=true) :
    eval H (annotatedWith D rust P)=eval H (recorded D (build D) P) ∨
      bad H (eval H P).2.physical.bytes (eval H P).2.stored := by
  have inv : AnnotationInvariant rust := fun _ _=>physical _ _ rfl rfl
  have rawAccept : (eval H (rust (eval H P).2)).2=true := by
    simpa only [annotated_eval D rust inv P H,F3T_TwoPass.original_eval] using accepted
  rcases carried c D rust physical bad join _ (carrier H) H rawAccept with joined | collision
  · left
    rw [annotated_eval D rust inv P H,recorded_eval]
    simp only [F3T_TwoPass.original_eval,F3T_Experiment.original_eval,joined]
  · exact Or.inr collision

#print axioms annotated_or_collision
end AspisR1.F3U_TwoPass
end
