import RPz8_ARX_TraceSupport
import RPz8_ARU_PartialFactory
import RPz8_ARW_Carrier
import RPz8_ARW_RuntimeDomain
import RPz8_ARV_Constant
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_AdmittedRuntime
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

/-- A completed cylinder belongs to the approved admitted game exactly when
it has its own bank tuple, two admissions, accepted native pair and persistence.
The existential contains those witnesses, not an attacker promise. -/
def permitted (v : View Bytes State (GExq_AccountExperiment.Outcome A)) : Prop :=
  ∃ H, Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a) = v

/-- Unnormalised admitted-world observer. No ROM probability is conditioned on
successful admission: outside-game cylinders have mass zero. -/
def runtime : F3T_Runtime.Runtime :=
  bind (OracleProgramRecording.record (ART_PartialAccount.account
    (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)) fun v =>
      .done (if permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a v then
        some (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input
          (FIp_Install.configuration err c r) (submitted v.2.1)),accepted v.2)) else none)

variable (extraction : S2W_DigestExtraction.AeneasExtraction
    (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)

include extraction
theorem permitted_iff (H : Bytes → State) :
    permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)) ↔
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  constructor
  · rintro ⟨K,⟨n⟩,same⟩
    exact ARU_PartialFactory.original L copy allocator c err r native1 native2 hashv extraction a K H n
      (ARX_TraceSupport.consistent _ K H (congrArg Prod.fst same))
  · intro n
    exact ⟨H,n,rfl⟩

theorem evaluation (H : Bytes → State) :
    eval H (runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      let v := eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)
      (v.1,if Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
        then (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r)
          hashv copy allocator CPH_Program.verifier a)).2 else none) := by
  simp only [runtime,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]
  rw [permitted_iff L copy allocator c err r native1 native2 hashv a extraction H]
  rw [ART_Runtime.eval_runtime]

theorem on_admitted (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    eval H (runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      eval H (ART_Runtime.runtime (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a) := by
  rw [evaluation L copy allocator c err r native1 native2 hashv a extraction H,if_pos ⟨n⟩,
    ART_Runtime.eval_runtime]

theorem outside (H : Bytes → State)
    (no : ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)) :
    (eval H (runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = none := by
  rw [evaluation L copy allocator c err r native1 native2 hashv a extraction H,if_neg no]

theorem excludes_poison (i : FirstInputs A) (j : SecondInputs A) (H : Bytes → State) :
    (eval H (runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv
      (ARV_Constant.adversary i (ARV_Constant.poison j)))).2 = none :=
  outside L copy allocator c err r native1 native2 hashv _ extraction H
    (ARV_Constant.no_support L copy allocator c err r native1 native2 hashv i j H)

#print axioms permitted_iff
#print axioms evaluation
#print axioms on_admitted
#print axioms outside
#print axioms excludes_poison
end AspisR1.ARX_AdmittedRuntime
end
