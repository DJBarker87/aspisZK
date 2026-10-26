import ARV_PoisonNative
import ARV_NativePartial
import ARQ_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Constant
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment

def adversary {A : Type} (i : FirstInputs A) (j : SecondInputs A) : Adversary A :=
  ⟨.done i,fun _ _ _ _ => .done j⟩

def poison {A : Type} (j : SecondInputs A) : SecondInputs A :=
  {j with entry := ARV_Poison.entry j.entry}

theorem no_support {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (i : FirstInputs A) (j : SecondInputs A) (H : Bytes → State) :
    ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv
      (adversary i (poison j)) H) := by
  rintro ⟨n⟩
  exact ARV_Poison.no_admission L j.entry n.entry.w2 7 n.entry.admission2

theorem accepted {A C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (H : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv H)
    (i : FirstInputs A) (j : SecondInputs A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (yes1 : first native1 copy allocator i.entry CPH_Program.verifier i.data i.state =
      ok (.Ok (saved,post1,final1)))
    (yes2 : second native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state =
      ok (.Ok (post2,final2))) :
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier (adversary i (poison j)))).2 = true := by
  let cfg := FIp_Install.configuration err c r
  have ext : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
        cfg.query cfg.geometry cfg.boundaries cfg.std) native1 native2 hashv := by
    rw [←ARQ_Installation.dictionary err c r]
    exact extraction
  have f := ARV_NativePartial.first cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
    cfg.query cfg.geometry cfg.boundaries cfg.std hashv native1 native2 ext H syscall
    copy allocator i.entry CPH_Program.verifier i.data i.state saved post1 final1 yes1
  have s := ARV_NativePartial.second cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
    cfg.query cfg.geometry cfg.boundaries cfg.std hashv native1 native2 ext H syscall
    allocator (ARV_Poison.entry j.entry) CPH_Program.verifier j.data j.slot j.state
    (ARV_Poison.entry j.entry).heap final2
    (ARV_PoisonNative.accepted native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state final2 post2 yes2)
  unfold ART_PartialAccount.account adversary
  simp only [eval_bind,eval,ARS_NativeAccount.firstSyntax,ARS_NativeAccount.secondSyntax,poison]
  rw [f]
  simp only [eval_bind,eval,ARS_NativeAccount.secondSyntax,poison]
  rw [s]
  rfl

#print axioms no_support
#print axioms accepted
end AspisR1.ARV_Constant
end
