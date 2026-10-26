import RPz7_F3T_CanonicalJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_CollisionJoin
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_Carried

/-- Byte-indexed collision exception. The event must later be associated with
and charged in the SAME source/account experiment; this type alone does neither. -/
abbrev Exception := (Bytes → State) → Bytes → Bytes → Prop

def Join {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (bad : Exception) : Prop :=
  ∀ (s : Submission) H,(eval H (rust (input c s))).2=true →
    eval H (rust (input c s))=eval H (F3_Model.verifier D (input c s)) ∨ bad H s.publicBytes s.stored

theorem carried {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : F3T_CanonicalJoin.Physical rust)
    (bad : Exception) (join : Join c D rust bad) (i : F3_Model.Input) (carrier : Carried c i)
    (H : Bytes → State) (accepted : (eval H (rust i)).2=true) :
    eval H (rust i)=eval H (F3_Model.verifier D i) ∨ bad H i.physical.bytes i.stored := by
  obtain ⟨s,sem,pub,stored,rows⟩ := carrier
  have source := physical i (input c s) (congrArg F3_Model.PhysicalPublic.bytes pub) stored
  have model : F3_Model.verifier D i=F3_Model.verifier D (input c s) := by
    unfold F3_Model.verifier OraclePortStoredExperimentC4.verifier
    rw [sem,pub,stored]
    exact OraclePortCanon.verifier_congr D _ _ _ _ rows
  have result := join s H (source ▸ accepted)
  rw [source,model,pub,stored]
  exact result

#print axioms carried
end AspisR1.F3U_CollisionJoin
end
