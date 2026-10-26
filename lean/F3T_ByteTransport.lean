import F3T_CanonicalJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ByteTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried F3T_CanonicalJoin

theorem annotated_eq {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : Prover)
    (carried : ∀ H,Carried c (eval H P).2) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D rust P)).2.2=true) :
    eval H (annotatedWith D rust P)=eval H (recorded D (build D) P) := by
  have inv : AnnotationInvariant rust := fun _ _=>physical _ _ rfl rfl
  rw [F3T_TwoPass.annotated_eval D rust inv P H] at accepted ⊢
  have before : (eval H (originalWith rust P)).2.2=true := accepted
  have rawAccept : (eval H (rust (eval H P).2)).2=true := by
    simpa only [F3T_TwoPass.original_eval] using before
  have joined := carried_join c D rust physical raw _ (carried H) H rawAccept
  have first : eval H (originalWith rust P)=eval H (original D P) := by
    rw [F3T_TwoPass.original_eval,F3T_Experiment.original_eval,joined]
  have second : Carried c (eval H (original D P)).2.1 := by
    simpa only [F3T_Experiment.original_eval] using carried H
  rw [first,F3T_Experiment.recorded_eval]
  dsimp only
  have acceptSecond : (eval H (rust (eval H (original D P)).2.1)).2=true := by
    rw [F3T_Experiment.original_eval];exact rawAccept
  rw [carried_join c D rust physical raw _ second H acceptSecond]

theorem recovered {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))).2.2=true) :
    OraclePortRefineJoin.RecoveredInputAgreement
      (view (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))))
      (view (eval H (recorded D (build D) (F3T_Canon.canon (lift c P))))) := by
  rw [annotated_eq c D rust physical raw _ (canon_lift_carried c P) H accepted]
  exact ⟨rfl,rfl,rfl⟩

#print axioms annotated_eq
#print axioms recovered
end AspisR1.F3T_ByteTransport
end
