import RPz8_F3V_DigestCompatibility
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_EvidenceCalls
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem preparation {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) :
    AspisR1CurrentCaller.verifier.candidate.prepare
      (RowShape_InstalledSlots.verifierOps (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () none
      (Array.repeat 29#usize e.run.zero)=ok (.Ok e.run.p,e.run.scratch) := by
  rw [Uni_Install.compose_tx1]
  exact e.run.prepare_call

theorem length {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) : e.proof.val.length=57607 := by
  simpa only [bytesOf,List.length_map] using ((OraclePortHeader.accepts_iff _).mp e.header).1

#print axioms preparation
#print axioms length
end AspisR1.F3V_EvidenceCalls
end
