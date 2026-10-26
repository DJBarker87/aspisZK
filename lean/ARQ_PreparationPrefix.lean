import ARQ_FirstMatches
import F3X_Preparation
import AuS1_Observe
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_PreparationPrefix
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution GExq_AccountExperiment DrvC_Installation F3V_RunEvidence

/-- The canonical preparation occurs in the ACTUAL account TX1, before the
adaptive second choice. This is a prefix of that wrapper, with all later
reads retained. It is stronger than inclusion in a separately run source. -/
theorem first_prefix {A F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State)
    (success : (eval H (firstCode c hashv copy allocator id i)).2 = ok (.Ok (saved,post,final)))
    (e : Evidence c B (submitted i) H)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none = ok (.Ok e.saved)) :
    saved = e.saved ∧ ∃ tail,
      (eval H (firstCode c hashv copy allocator id i)).1 =
        (eval H (F3X_Preparation.program c (submitted i))).1 ++ tail := by
  have same := ARQ_FirstMatches.same c aligned B hashv copy allocator id i saved post final H success e first
  have whole := congrArg Prod.fst (F3U_ReifyExact.exact
    (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize) H)
  dsimp only at whole
  rw [F3W_FirstLog.log c B (submitted i) H e hashv first] at whole
  have lowered := AuS1_Observe.lower (F3U_Oracle.hashv H)
    (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.proof () (Array.repeat 29#usize e.run.zero))
    (AuS1_Prepare.uniform _ _ _ _ (F3U_Oracle.hashv H) (fun _ _ => rfl) _ _ _ _) []
  rw [show SdkC_Source.readLog [] = [] from rfl,List.nil_append] at lowered
  change _ = AuS1_Recovery.log _ _ _ _ _ _ _ _ at lowered
  rw [lowered] at whole
  refine ⟨same.1,?_⟩
  rw [F3X_Preparation.on_evidence c B (submitted i) H e]
  exact ⟨_,same.2.trans whole⟩

#print axioms first_prefix
end AspisR1.ARQ_PreparationPrefix
end
