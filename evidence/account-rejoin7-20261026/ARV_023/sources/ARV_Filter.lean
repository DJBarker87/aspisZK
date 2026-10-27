import ARV_ObservedSupport
import ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Filter
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

/-- Unadopted mathematical observer. Retains rejected views and all query
prefixes; drops only accepted observations without a bank-supported cylinder.
The Eligible test is noncomputable, not a claim about shipped source. -/
def runtime : F3T_Runtime.Runtime :=
  AspisV8R19.OracleProgramOps.bind
    (OracleProgramRecording.record (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)) fun v =>
    .done (if SCE_Experiment.accepted v.2 = false ∨
        ARV_ObservedSupport.Eligible (Tx := Tx) L copy allocator c err r native1 native2 hashv a v
      then some (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input (FIp_Install.configuration err c r)
        (submitted v.2.1)),SCE_Experiment.accepted v.2)) else none)

theorem eval_runtime (H : Bytes → State) :
    eval H (runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      let v := eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)
      (v.1,if SCE_Experiment.accepted v.2 = false ∨
        ARV_ObservedSupport.Eligible (Tx := Tx) L copy allocator c err r native1 native2 hashv a v
      then some (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input (FIp_Install.configuration err c r)
        (submitted v.2.1)),SCE_Experiment.accepted v.2)) else none) := by
  simp only [runtime,AspisV8R19.OracleProgramOps.eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

theorem query_log (H : Bytes → State) :
    (eval H (runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).1 =
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)).1 := by
  rw [eval_runtime]

#print axioms eval_runtime
#print axioms query_log
end AspisR1.ARV_Filter
end
