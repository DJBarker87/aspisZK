import SCH_AcceptedSources
import SCH_SourceCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_AccountCuts
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation

/-- Response-selected source cuts in EVERY oracle world, obtained from that
world's actual accepted account; no fixed native observations are generalized. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) :
    ∀ H : Bytes → State,
    SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      SourceCuts (SCH_IdealSdk.dictionary c hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes)
        saved f s := by
  intro H success
  obtain ⟨saved,post,final,one,two⟩ := SCH_AcceptedSources.accepted c hashv copy allocator id a H success
  obtain ⟨f,s,cuts⟩ := SCH_SourceCuts.pair _ id _ _ _ _ _ saved one two
  exact ⟨saved,post,final,f,s,cuts⟩

#print axioms accepted
end AspisR1.SCH_AccountCuts
end
