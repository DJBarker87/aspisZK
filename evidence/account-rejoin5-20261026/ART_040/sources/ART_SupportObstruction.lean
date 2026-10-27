import ART_SyscallObstruction
import ARS_Coverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_SupportObstruction
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open SCE_Experiment

theorem no_entry {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest) (returned : hashv parts = ok digest)
    (value : State) (different : value ≠ native (flatten parts)) :
    ¬ Nonempty (ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (ART_QueryCylinder.change native (flatten parts) value)) := by
  rintro ⟨n⟩
  exact ART_SyscallObstruction.no_native_world hashv native syscall parts digest returned value different
    ⟨n.sha256,n.p1,n.syscall⟩

#print axioms no_entry
end AspisR1.ART_SupportObstruction
end
