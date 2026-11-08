import NNH_Run5bSplit
import NNH_Run5bHeadline
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNW_Events
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_Run5bCtx NNH_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 Rc2_Events.Facts (configuration c) (hashv c) n1 n2 copy NNE_AbortIndicator.allocator CPH_Program.verifier c.sha256 c.world.saved := by
 exact Rc2_Events.derive _ (hashv c) n1 n2 ext copy NNE_AbortIndicator.allocator
    CPH_Program.verifier c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256)
    (DGP_HostDigest.syscall c.sha256) c.world.saved
#print axioms produce
end AspisR1.NNW_Events
end
