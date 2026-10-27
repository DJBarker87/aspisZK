import ART_OriginalLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_OutcomeMixture
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open SCE_Experiment

/-- Any supplied mixture is transported on its original support. This does
not assert that one fixed-native cylinder has probability one under the ROM. -/
theorem law {A F C Coins : Type} [Fintype Coins] [Nonempty Coins]
    (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native : Coins → Bytes → State) (worlds : Coins → Bytes → State)
    (certificates : ∀ coin, ART_PartialAccount.Certificate c hashv copy allocator id a (native coin) (worlds coin))
    (observe : GExq_AccountExperiment.Outcome A → Nat → Rat) :
    mean (fun coin => observe (eval (worlds coin) (ART_PartialAccount.account c hashv copy allocator id a)).2
      (eval (worlds coin) (ART_PartialAccount.account c hashv copy allocator id a)).1.length) =
    mean (fun coin => observe (ARS_NativeAccount.run c hashv copy allocator id a (native coin)).2
      (ARS_NativeAccount.attempts c hashv copy allocator id a (native coin))) := by
  apply mean_congr
  intro coin
  exact ART_OriginalLaw.exact c hashv copy allocator id a (native coin) (worlds coin) (certificates coin) observe

#print axioms law
end AspisR1.ART_OutcomeMixture
end
