import NNQ_Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

theorem firstSyntax_eq (i : GExq_AccountExperiment.FirstInputs A) :
    ARS_NativeAccount.firstSyntax (withDigest c o) hv copy allocator id i =
    ARS_NativeAccount.firstSyntax c hv copy allocator id i := by
  unfold ARS_NativeAccount.firstSyntax GExq_InstalledWrapper.first
  exact congrArg (fun body => GExq_WrapperCode.first body copy allocator i.entry i.state)
    (caller_first_eq c o hv id i.entry.first i.data)

theorem secondSyntax_eq (i : GExq_AccountExperiment.SecondInputs A) :
    ARS_NativeAccount.secondSyntax (withDigest c o) hv allocator id i =
    ARS_NativeAccount.secondSyntax c hv allocator id i := by
  unfold ARS_NativeAccount.secondSyntax GExq_InstalledWrapper.second
  exact congrArg (fun body => GExq_WrapperCode.second body allocator i.entry i.state)
    (caller_second_eq c o hv id (i.entry.second secondSizes) i.data i.slot)

theorem account_withDigest (a : SCE_Experiment.Adversary A) :
    ART_PartialAccount.account (withDigest c o) hv copy allocator id a =
    ART_PartialAccount.account c hv copy allocator id a := by
  simp only [ART_PartialAccount.account, firstSyntax_eq c o hv copy allocator id,
    secondSyntax_eq c o hv allocator id]
#print axioms firstSyntax_eq
#print axioms secondSyntax_eq
#print axioms account_withDigest
end AspisR1.NNQ_HostDigest
end
