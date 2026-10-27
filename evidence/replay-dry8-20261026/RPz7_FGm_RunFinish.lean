import RPz7_SAG_NativeFull
import RPz7_F3V_Checkpoint
import RPz7_FGl_FinishProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_RunFinish
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem reached {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) (prior : Program Bytes State Unit)
    (p : OraclePortCompactDraft.Parsed) (parser : OraclePortCompactDraft.parse (bytesOf e.proof.val)=some p)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domain : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned) :
    ∃ t : Cons_Native.Witness,
      Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
        (D2 c H) () e.pub e.proof e.saved.deref t ∧
      Cons_NativeBuild.Aux c.reserved c.query c.geometry (D2 c H) () e.pub e.proof e.saved.deref t ∧
      SAG_NativeFull.Shape (Tx2N_Execution.control
        (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
        c.reserved c.query c.geometry) e.proof t ∧
      FGl_Finish.Outcome c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
        e.proof e.saved H (bytesOf e.proof.val) (bytesOf e.pub.val) e.run.p p
        (F3V_Checkpoint.trace c B s H e prior) := by
  have second := e.second
  rw [F3V_SecondSlots.same] at second
  obtain ⟨t,calls,aux,shape⟩ := SAG_NativeFull.accepted (Op5T_Concrete.stage (AuS1_Install.base c.stageBase))
    c.finish c.reserved c.query c.geometry (D2 c H) () e.pub e.proof e.saved.deref second
  obtain ⟨frame,read,target,auth⟩ := F3V_Authenticated.recovered c B s H e prior p parser
  refine ⟨t,calls,aux,shape,?_⟩
  exact FGl_FinishProof.strengthen (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved
    c.query ports c.geometry canonical domain multiply one inverse (D2 c H) () e.pub e.proof e.saved.deref e.saved H
    _ _ e.run.p p (F3V_Checkpoint.trace c B s H e prior) frame
    (OraclePortCompactDraft.parse_header _ _ parser).2 rfl (F3V_EvidenceCalls.length c B s H e) t calls aux auth

#print axioms reached
end AspisR1.FGm_RunFinish
end
