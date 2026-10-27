import RPz8_ARQ_PreparationPrefix
import RPz8_ARQ_AccountPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_AccountPreparation
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution DrvC_Installation F3V_RunEvidence

theorem included {A F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State)
    (success : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 = ok (.Ok (saved,post,final)))
    (e : Evidence c B (submitted (eval H a.first).2) H)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none = ok (.Ok e.saved)) :
    saved = e.saved ∧
    ∀ addr, FS2.Duplex.Read (eval H (F3X_Preparation.program c (submitted (eval H a.first).2))).1 addr →
      FS2.Duplex.Read (eval H (account c hashv copy allocator id a)).1 addr := by
  obtain ⟨same,tail,traceEq⟩ := ARQ_PreparationPrefix.first_prefix c aligned B hashv copy allocator id
    (eval H a.first).2 saved post final H success e first
  refine ⟨same,?_⟩
  intro addr read
  apply ARQ_AccountPrefix.first_read c hashv copy allocator id a H saved post final success addr
  rw [traceEq]
  change addr ∈ (_ ++ tail).map Prod.fst
  rw [List.map_append]
  exact List.mem_append_left _ read

#print axioms included
end AspisR1.ARQ_AccountPreparation
end
