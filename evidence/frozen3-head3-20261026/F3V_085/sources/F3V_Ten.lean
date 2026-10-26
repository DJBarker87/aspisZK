import F3V_Authenticated
import F3N_Ten
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Ten
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem outcome {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) (prior : Program Bytes State Unit)
    (p : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse (bytesOf e.proof.val)=some p) :
    let trace := (eval H prior).1 ++ AuS1_Recovery.log
      (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std (D1 c H)
      (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero)
    Cons_Ten.Outcome e.run H trace p := by
  obtain ⟨frame,read,target,recover⟩ := F3V_Authenticated.recovered c B s H e prior p parser
  apply F3N_Ten.transport e.run (F3V_EvidenceCalls.length c B s H e) H _ p
  intro data rho q prepare
  rcases recover data rho q prepare with bad | good
  · exact Or.inl bad
  · exact Or.inr ⟨OraclePortAllSelectedRecoveryC6.recovered _ frame p 2,good⟩

#print axioms outcome
end AspisR1.F3V_Ten
end
