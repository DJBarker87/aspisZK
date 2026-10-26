import ART_AdversaryWork
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_WrapperBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount ART_PartialAccount
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

theorem first (i : FirstInputs A) (H : Bytes → State) :
    (eval H (wrapper hashv (firstSyntax c hashv copy allocator id i))).1.length ≤ 1018 :=
  (ART_PrefixCoupling.cost hashv H _).trans
    (RawJ_InstalledBudget.first c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv copy allocator i.entry id i.data i.state H)

theorem second (i : SecondInputs A) (H : Bytes → State) :
    (eval H (wrapper hashv (secondSyntax c hashv allocator id i))).1.length ≤ 903 :=
  (ART_PrefixCoupling.cost hashv H _).trans
    (RawJ_InstalledBudget.second c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv allocator i.entry id i.data i.slot i.state H)

#print axioms first
#print axioms second
end AspisR1.ART_WrapperBudget
end
