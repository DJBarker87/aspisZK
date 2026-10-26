import ARU_OriginalSupport
import ARU_Factory
import ART_QueryRestricted
import ARS_WorldCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_ObstructionResolved
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
/-- Regression witness for the OLD interface obstruction: the SAME installed
query-consistent execution now has At support even when NativeAt is impossible.
No new oracle agreement is imposed at the unissued address. -/
theorem installed {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native : Bytes → State)
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest) (returned : hashv parts = ok digest)
    (unissued : AspisV8R19.SqueezeOracleBridge.flatten parts ∉ (eval native
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).1.map Prod.fst)
    (value : State) (different : value ≠ native (AspisV8R19.SqueezeOracleBridge.flatten parts)) :
    let H := ART_QueryCylinder.change native (AspisV8R19.SqueezeOracleBridge.flatten parts) value
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    ¬ Nonempty (ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  have old := ART_QueryRestricted.installed L copy allocator c err r native1 native2 hashv extraction a native n
    parts digest returned unissued value different
  have entry := (ARS_Coverage.deployed L copy allocator c err r native1 native2 hashv extraction a native native n
    (by intro address member; rfl)).1
  obtain ⟨entry⟩ := entry
  have syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native :=
    ⟨fun p d returned => (n.syscall.returningValue p d returned).trans (n.p1.realization _)⟩
  obtain ⟨original⟩ := ARU_OriginalSupport.original L copy allocator c err r native1 native2 hashv extraction a native entry syscall
  exact ⟨ARU_Factory.deployed L copy allocator c err r native1 native2 hashv extraction a native _ original
    (ARS_WorldCylinder.agrees_of_same native _ _ old.2.1),old.2.2⟩

#print axioms installed
end AspisR1.ARU_ObstructionResolved
end
