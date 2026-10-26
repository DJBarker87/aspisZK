import ARQ_ActualFirst
import F3W_Runs
import DrvC_Bytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_FirstMatches
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution GExq_AccountExperiment DrvC_Installation F3V_RunEvidence

/-- Identify the actual account first call with the standalone evidence on
its ORIGINAL submission. Determinism fixes its saved checkpoint as well.
No equality of full account and standalone logs is asserted. -/
theorem same {A F C : Type} (c : Configuration F C)
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
    saved = e.saved ∧
    (eval H (firstCode c hashv copy allocator id i)).1 =
      (eval H (SdkC_Oracle.program
        (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
          e.pub e.proof 10#usize))).1 := by
  obtain ⟨semantic,pub,proof,bytes,decoded,called,logs⟩ :=
    ARQ_ActualFirst.accepted c aligned hashv copy allocator id i saved post final H success
  have publicBytes := congrArg (fun s : F3T_ByteCarrier.Submission => s.publicBytes) bytes
  have proofBytes := congrArg (fun s : F3T_ByteCarrier.Submission => s.stored) bytes
  have pubEq := DrvC_Bytes.slice_injective pub e.pub (publicBytes.symm.trans e.pubBytes.symm)
  have proofEq := DrvC_Bytes.slice_injective proof e.proof (proofBytes.symm.trans e.proofBytes.symm)
  subst pub; subst proof
  have semanticEq := Option.some.inj (Result.ok.inj (decoded.symm.trans e.decoded))
  subst semantic
  have savedEq := core.result.Result.Ok.inj (Result.ok.inj (called.symm.trans first))
  exact ⟨savedEq,logs⟩

#print axioms same
end AspisR1.ARQ_FirstMatches
end
