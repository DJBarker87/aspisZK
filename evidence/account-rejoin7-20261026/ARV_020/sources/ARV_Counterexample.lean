import ARV_AdaptiveAccepted
import ARV_LogChange
import ARU_OriginalFactory
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Counterexample
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open GExq_AccountExperiment SCE_Experiment

theorem accepted_without_support {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (i : FirstInputs A) (j : SecondInputs A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (yes1 : first native1 copy allocator i.entry CPH_Program.verifier i.data i.state =
      ok (.Ok (saved,post1,final1)))
    (yes2 : second native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state =
      ok (.Ok (post2,final2)))
    (address : Bytes) (value : State) (different : value ≠ native address)
    (fresh1 : address ∉ (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier i) []).2.map (fun q => flatten q.parts))
    (fresh2 : address ∉ (SdkC_Source.run hashv
      (ARS_NativeAccount.secondSyntax (FIp_Install.configuration err c r) hashv allocator CPH_Program.verifier (ARV_Constant.poison j)) []).2.map (fun q => flatten q.parts)) :
    let a := ARV_Adaptive.adversary i j address (native address)
    let H := ART_QueryCylinder.change native address value
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = true ∧
    ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    ¬ ARU_AllWorld.Supported (Tx := Tx) L copy allocator c err r native1 native2 hashv a := by
  dsimp only
  have mismatch : (ART_QueryCylinder.change native address value) address ≠ native address := by
    simpa only [ART_QueryCylinder.change,if_pos rfl,ite_true] using different
  have f := ARV_LogChange.agrees native address value _
    (ART_NativeAgreement.issued hashv native syscall _) fresh1
  have s := ARV_LogChange.agrees native address value _
    (ART_NativeAgreement.issued hashv native syscall _) fresh2
  have yes := ARV_AdaptiveAccepted.accepted copy allocator c err r native1 native2 hashv extraction _
    address (native address) mismatch i j saved post1 post2 final1 final2 f s yes1 yes2
  have no := ARV_Adaptive.no_support (Tx := Tx) L copy allocator c err r native1 native2 hashv
    i j address (native address) _ mismatch
  exact ⟨yes,no,fun support => no (support _ yes)⟩

#print axioms accepted_without_support
end AspisR1.ARV_Counterexample
end
