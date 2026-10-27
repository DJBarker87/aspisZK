import F3U_TwoPass
import F3T_InstalledRecovered
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Recovered
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried F3U_CollisionJoin

theorem inputs_or_collision {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : F3T_CanonicalJoin.Physical rust)
    (bad : Exception) (join : Join c D rust bad) (P : ByteProver) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))).2.2=true) :
    OraclePortRefineJoin.RecoveredInputAgreement
      (view (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))))
      (view (eval H (recorded D (build D) (F3T_Canon.canon (lift c P))))) ∨
    bad H (eval H P).2.publicBytes (eval H P).2.stored := by
  rcases F3U_TwoPass.annotated_or_collision c D rust physical bad join _ (canon_lift_carried c P) H accepted with joined | collision
  · exact Or.inl (joined ▸ ⟨rfl,rfl,rfl⟩)
  · right
    simpa only [F3T_Canon.canon_eval,lift_eval,F3T_Canon.canonInput,input] using collision

#print axioms inputs_or_collision
end AspisR1.F3U_Recovered
end
