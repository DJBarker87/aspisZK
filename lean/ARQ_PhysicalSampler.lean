import ARQ_PreparationPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_PhysicalSampler
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution DrvC_Installation F3V_RunEvidence

theorem chronological {A F C : Type} (c : Configuration F C)
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
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none = ok (.Ok e.saved))
    (sampler : (eval H (F3X_Preparation.program c (submitted (eval H a.first).2))).1 =
      (eval H (F3J_SamplerRun.program
        (F3T_Canon.canonInput (F3T_ByteCarrier.input c (submitted (eval H a.first).2))).proof 0 33
        (FS.emptyPrefix (F3T_ByteCarrier.input c (submitted (eval H a.first).2)).semantic.value))).1) :
    ∃ tail, (eval H (account c hashv copy allocator id a)).1 =
      ((eval H a.first).1 ++
        (eval H (F3J_SamplerRun.program
          (F3T_Canon.canonInput (F3T_ByteCarrier.input c (submitted (eval H a.first).2))).proof 0 33
          (FS.emptyPrefix (F3T_ByteCarrier.input c (submitted (eval H a.first).2)).semantic.value))).1) ++ tail := by
  obtain ⟨same,tail,traceEq⟩ := ARQ_PreparationPrefix.first_prefix c aligned B hashv copy allocator id
    (eval H a.first).2 saved post final H success e first
  rw [accepted_eval c hashv copy allocator id a H saved post final success,traceEq,sampler]
  refine ⟨tail ++ ((eval H (a.second (eval H a.first).2 saved post final)).1 ++
    (eval H (secondCode c hashv allocator id (eval H (a.second (eval H a.first).2 saved post final)).2)).1),?_⟩
  simp only [List.append_assoc]

#print axioms chronological
end AspisR1.ARQ_PhysicalSampler
end
