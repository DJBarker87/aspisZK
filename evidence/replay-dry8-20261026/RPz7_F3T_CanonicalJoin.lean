import RPz7_F3T_Carried
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_CanonicalJoin
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried

def AcceptedVerifierJoin {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop :=
  ∀ (s : Submission) H,(eval H (rust (input c s))).2=true →
    eval H (rust (input c s))=eval H (F3_Model.verifier D (input c s))

def Physical (rust : Verifier) : Prop := ∀ i j : F3_Model.Input,
  i.physical.bytes=j.physical.bytes → i.stored=j.stored → rust i=rust j

theorem carried_join {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (join : AcceptedVerifierJoin c D rust) (i : F3_Model.Input) (carried : Carried c i)
    (H : Bytes → State) (accepted : (eval H (rust i)).2=true) :
    eval H (rust i)=eval H (F3_Model.verifier D i) := by
  obtain ⟨s,sem,pub,stored,rows⟩ := carried
  have source := physical i (input c s) (congrArg F3_Model.PhysicalPublic.bytes pub) stored
  have model : F3_Model.verifier D i=F3_Model.verifier D (input c s) := by
    unfold F3_Model.verifier OraclePortStoredExperimentC4.verifier
    rw [sem,pub,stored]
    exact OraclePortCanon.verifier_congr D _ _ _ _ rows
  rw [source] at accepted ⊢
  rw [model]
  exact join s H accepted

#print axioms carried_join
end AspisR1.F3T_CanonicalJoin
end
