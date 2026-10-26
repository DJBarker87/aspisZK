import ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_FirstProjection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment

theorem original {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) (H : Bytes → State) :
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2.1 = (eval H a.first).2 := by
  unfold ART_PartialAccount.account
  simp only [eval_bind]
  split <;> simp only [eval_bind,eval]

#print axioms original
end AspisR1.ART_FirstProjection
end
