import ART_Coverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_Cost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount ART_PartialAccount
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

theorem represented (native H : Bytes → State) :
    (ART_PartialAccount.represented c hashv copy allocator id a native H).1.length =
      attempts c hashv copy allocator id a native := by
  unfold ART_PartialAccount.represented attempts
  dsimp only
  cases reply : (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 with
  | fail error => simp only [reply,List.length_append,ART_PartialProgram.attempted,List.length_map]
  | div => simp only [reply,List.length_append,ART_PartialProgram.attempted,List.length_map]
  | ok result => cases result <;> simp only [reply,List.length_append,ART_PartialProgram.attempted,List.length_map]

theorem exact (native H : Bytes → State)
    (certificate : ART_PartialAccount.Certificate c hashv copy allocator id a native H) :
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).1.length =
      attempts c hashv copy allocator id a native := by
  rw [ART_Coverage.execution c hashv copy allocator id a native H certificate]
  exact represented c hashv copy allocator id a native H

#print axioms represented
#print axioms exact
end AspisR1.ART_Cost
end
