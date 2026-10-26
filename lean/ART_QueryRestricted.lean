import ART_SupportObstruction
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_QueryRestricted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open SCE_Experiment

/-- Full installed conditional obstruction: a query-consistent SAME accepted
execution has the required bank/admission witnesses but cannot inhabit the old
NativeAt record. The sole contradiction is its global native-world interface;
this does not refute a properly weakened query-only clean transport theorem. -/
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
    (unissued : flatten parts ∉ (eval native
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).1.map Prod.fst)
    (value : State) (different : value ≠ native (flatten parts)) :
    let H := ART_QueryCylinder.change native (flatten parts) value
    Nonempty (ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval native (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) ∧
    ¬ Nonempty (ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  let H := ART_QueryCylinder.change native (flatten parts) value
  have same := ART_QueryCylinder.outside
    (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
    native (flatten parts) value unissued
  have supported := ARS_Coverage.deployed L copy allocator c err r native1 native2 hashv extraction a native H n same
  refine ⟨supported.1,supported.2.1,?_⟩
  have syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native :=
    ⟨fun p d returned => (n.syscall.returningValue p d returned).trans (n.p1.realization _)⟩
  exact ART_SupportObstruction.no_entry L copy allocator c err r native1 native2 hashv a native syscall
    parts digest returned value different

#print axioms installed
end AspisR1.ART_QueryRestricted
end
