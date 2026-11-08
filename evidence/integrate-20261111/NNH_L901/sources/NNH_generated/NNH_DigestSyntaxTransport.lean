import NNH_DigestSyntaxSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_DigestSyntaxTransport
open Aeneas Aeneas.Std Result CheckpointBytes5Effect S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem lower {A : Type} (i1 i2 : {B : Type} → S2W_Trace.Call B → Code B)
 (same : ∀ {B : Type} (call : S2W_Trace.Call B), i1 call = i2 call)
 (code : S2W_Trace.Code A) : GExq_OuterLower.lower i1 code = GExq_OuterLower.lower i2 code := by
 induction code with
 | done a => rfl
 | step r k ih =>
  simp only [GExq_OuterLower.lower]
  congr 1
  funext value
  exact ih value
 | call op k ih =>
  simp only [GExq_OuterLower.lower,same op]
  congr 1
  funext value
  exact ih value

theorem child {F C A : Type} (c : DrvC_Installation.Configuration F C)
 (h1 h2 : SdkC_Source.Parts → Result SdkC_Source.Digest) (call : S2W_Trace.Call A) :
 GExq_ChildCode.execute c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry
  c.boundaries c.std h1 call =
 GExq_ChildCode.execute c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry
  c.boundaries c.std h2 call := by
 cases call <;> simp only [GExq_ChildCode.execute]
 all_goals try exact rfl

theorem first {F C A : Type} (c : DrvC_Installation.Configuration F C)
 (h1 h2 : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (alloc : Allocator A) (id : S2W_ExtractionBoundary.Program)
 (i : GExq_AccountExperiment.FirstInputs A) :
 ARS_NativeAccount.firstSyntax c h1 copy alloc id i = ARS_NativeAccount.firstSyntax c h2 copy alloc id i := by
 unfold ARS_NativeAccount.firstSyntax GExq_InstalledWrapper.first GExq_Caller.first
 rw [lower _ _ (child c h1 h2)]

theorem second {F C A : Type} (c : DrvC_Installation.Configuration F C)
 (h1 h2 : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (alloc : Allocator A) (id : S2W_ExtractionBoundary.Program)
 (j : GExq_AccountExperiment.SecondInputs A) :
 ARS_NativeAccount.secondSyntax c h1 alloc id j = ARS_NativeAccount.secondSyntax c h2 alloc id j := by
 unfold ARS_NativeAccount.secondSyntax GExq_InstalledWrapper.second GExq_Caller.second
 rw [lower _ _ (child c h1 h2)]
theorem account {F C : Type} (c : DrvC_Installation.Configuration F C)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (alloc : Allocator Bool) (id : S2W_ExtractionBoundary.Program) (a : SCE_Experiment.Adversary Bool)
 (sha256 : Bytes → State) (d0 : S2Z.Oracle.Digest) :
 ART_PartialAccount.account c (DGP_HostDigest.hashvInst sha256) copy alloc id a =
 ART_PartialAccount.account c (fun _ => .ok d0) copy alloc id a := by
 have wrapper : ∀ {A : Type} (code : Code A),
  ART_PartialAccount.wrapper (DGP_HostDigest.hashvInst sha256) code =
  ART_PartialAccount.wrapper (fun _ => .ok d0) code := by
  intro A code
  unfold ART_PartialAccount.wrapper
  rw [NNH_DigestProgramStatus.adapter_fixed sha256 d0]
 unfold ART_PartialAccount.account
 congr 1
 funext i
 rw [first c (DGP_HostDigest.hashvInst sha256) (fun _ => .ok d0),wrapper]
 congr 1
 funext reply
 split
 · congr 1
   funext j
   rw [second c (DGP_HostDigest.hashvInst sha256) (fun _ => .ok d0),wrapper]
 · rfl

theorem o1 : DGP_HostDigest.O1 := by
 intro C copy base err r sha256 d0 a Q
 unfold NNH_RecordedCharge.recorder NNH_RecordedCharge.source
 rw [account _ copy NNE_AbortIndicator.allocator CPH_Program.verifier
  (NNH_StateNormalize.normalize a) sha256 d0]

#print axioms account
#print axioms o1
#print axioms lower
#print axioms child
#print axioms first
#print axioms second
end AspisR1.NNH_DigestSyntaxTransport
end
