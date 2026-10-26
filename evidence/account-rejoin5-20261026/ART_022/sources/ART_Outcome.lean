import ART_Coverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_Outcome
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount ART_PartialAccount
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

theorem represented (native H : Bytes → State) :
    (ART_PartialAccount.represented c hashv copy allocator id a native H).2 =
    (ARS_NativeAccount.run c hashv copy allocator id a native).2 := by
  unfold ART_PartialAccount.represented ARS_NativeAccount.run
  dsimp only
  cases reply : (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 with
  | fail error => simp only [reply]
  | div => simp only [reply]
  | ok result => cases result <;> simp only [reply]

theorem exact (native H : Bytes → State)
    (certificate : ART_PartialAccount.Certificate c hashv copy allocator id a native H) :
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 =
      (ARS_NativeAccount.run c hashv copy allocator id a native).2 := by
  rw [ART_Coverage.execution c hashv copy allocator id a native H certificate]
  exact represented c hashv copy allocator id a native H

/-- Under the existing extraction boundary, partial native wrappers and the
failure-aware experiment agree on BOTH transaction Results, including aborts. -/
theorem native (nativeOracle H : Bytes → State)
    (certificate : ART_PartialAccount.Certificate c hashv copy allocator id a nativeOracle H)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv) :
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 =
      ARS_NativeOutcome.wrappers copy allocator id a native1 native2 nativeOracle :=
  (exact c hashv copy allocator id a nativeOracle H certificate).trans
    (ARS_NativeOutcome.source c hashv copy allocator id a native1 native2 nativeOracle extraction)

#print axioms represented
#print axioms exact
#print axioms native
end AspisR1.ART_Outcome
end
