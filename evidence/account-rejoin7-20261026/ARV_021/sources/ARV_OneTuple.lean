import ARV_Counterexample
import ARV_AdaptiveOriginal
import ARV_Fresh
import ARR_OffPath
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_OneTuple
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open GExq_AccountExperiment SCE_Experiment

theorem obstruction {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native : Bytes → State)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native) :
    ∃ b : Adversary A, Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv b native) ∧
      ∃ H : Bytes → State,
        SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
          hashv copy allocator CPH_Program.verifier b)).2 = true ∧
        ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv b H) ∧
        ¬ ARU_AllWorld.Supported (Tx := Tx) L copy allocator c err r native1 native2 hashv b ∧
        ¬ ARU_CoverageQuantifiers.OriginalCoverage (Tx := Tx) L copy allocator c err r native1 native2 hashv b := by
  let cfg := FIp_Install.configuration err c r
  let i := (eval native a.first).2
  let j := (eval native (a.second i n.entry.saved n.entry.post1 n.entry.final1)).2
  let log1 := (SdkC_Source.run hashv (ARS_NativeAccount.firstSyntax cfg hashv copy allocator CPH_Program.verifier i) []).2
  let log2 := (SdkC_Source.run hashv (ARS_NativeAccount.secondSyntax cfg hashv allocator CPH_Program.verifier (ARV_Constant.poison j)) []).2
  obtain ⟨address,fresh⟩ := ARV_Fresh.address
    (log1.map (fun q => flatten q.parts) ++ log2.map (fun q => flatten q.parts))
  have fresh1 : address ∉ log1.map (fun q => flatten q.parts) :=
    fun member => fresh (List.mem_append_left _ member)
  have fresh2 : address ∉ log2.map (fun q => flatten q.parts) :=
    fun member => fresh (List.mem_append_right _ member)
  obtain ⟨value,different⟩ := ARR_OffPath.different (native address)
  let b := ARV_Adaptive.adversary i j address (native address)
  have original := ARV_AdaptiveOriginal.original L copy allocator c err r native1 native2 hashv a native address n
  have bad := ARV_Counterexample.accepted_without_support (Tx := Tx) L copy allocator c err r native1 native2
    hashv extraction native syscall i j n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2
    n.entry.accepted1 n.entry.accepted2 address value different fresh1 fresh2
  refine ⟨b,original,ART_QueryCylinder.change native address value,bad.1,bad.2.1,bad.2.2,?_⟩
  intro coverage
  exact bad.2.2 ((ARU_CoverageQuantifiers.exact_iff L copy allocator c err r native1 native2 hashv extraction b).mp coverage)

#print axioms obstruction
end AspisR1.ARV_OneTuple
end
