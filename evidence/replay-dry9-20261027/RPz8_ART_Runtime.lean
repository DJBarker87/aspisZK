import RPz8_ART_Coverage
import RPz8_RPx_RejectMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_Runtime
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

/-- Failure-aware runtime view. CP bytes remain indexed by the bank entry,
not invented as an additional field of the existing RunView. -/
def runtime : F3T_Runtime.Runtime :=
  bind (OracleProgramRecording.record (ART_PartialAccount.account c hashv copy allocator id a)) fun v =>
    .done (some (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2)))

theorem eval_runtime (H : Bytes → State) :
    eval H (runtime c hashv copy allocator id a) =
      let v := eval H (ART_PartialAccount.account c hashv copy allocator id a)
      (v.1,some (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2))) := by
  simp only [runtime,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

theorem rejected (H : Bytes → State)
    (reject : accepted (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = false) :
    F3T_Runtime.runtimeMass (eval H (runtime c hashv copy allocator id a)) = 0 := by
  rw [eval_runtime]
  exact RPx_RejectMass.rejected _ reject

#print axioms eval_runtime
#print axioms rejected
end AspisR1.ART_Runtime
end
