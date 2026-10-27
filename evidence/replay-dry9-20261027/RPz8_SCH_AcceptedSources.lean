import RPz8_SCH_SourceFirst
import RPz8_SCH_SourceSecond
import RPz8_SCG_AcceptedPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_AcceptedSources
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Both per-world source calls, selected from the SAME ideal account run.
No native success or new game observation is a premise. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (success : SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true) :
    ∃ saved post final,
      AdapterRw.r1_pool_adapter.owned.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
        id (eval H a.first).2.entry.first (eval H a.first).2.data = ok (.Ok saved) ∧
      AdapterRw.r1_pool_adapter.owned.stage2_owned (SCH_IdealSdk.dictionary c hashv H)
        id ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes)
        (eval H (a.second (eval H a.first).2 saved post final)).2.data
        (eval H (a.second (eval H a.first).2 saved post final)).2.slot = ok (.Ok ()) := by
  obtain ⟨saved,post,final,post2,final2,first,second⟩ :=
    SCG_AcceptedPair.replies c hashv copy allocator id a H success
  exact ⟨saved,post,final,
    SCH_SourceFirst.accepted c hashv copy allocator id _ saved post final H first,
    SCH_SourceSecond.accepted c hashv allocator id _ post2 final2 H second⟩

#print axioms accepted
end AspisR1.SCH_AcceptedSources
end
