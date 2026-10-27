import BEj_LocalExport
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEj_SlotExport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- The recorder-facing packet: exact chronological cut, all attempted
occurrences, the source's concrete 900 bound and its ideal attempted prefix.
No claim is made that a physical cut inhabits this packet yet. -/
def Prefix (hashv : Parts → Result Digest) (H : Bytes → State)
    {Err : Type} (code : Code (core.result.Result Unit Err)) (before after : Log) : Prop :=
  after = before ++ BEi_RecorderCut.issued before after ∧
  BEi_RecorderCut.issued before after = (SdkC_Source.run hashv code []).2 ∧
  (BEi_RecorderCut.issued before after).length ≤ 900 ∧
  ∃ remaining,
    (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
      RPx_AttemptPrefix.addresses (BEi_RecorderCut.issued before after) ++ remaining

/-- Current batch uses the SAME current Prepared, root and initial recorder.
The physical boundary law is an explicit remaining proof obligation. -/
theorem current {S E : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest)
    (state : S) (before : Log) (native : BEh_Scope.Outcome S Unit E)
    (law : BEh_Scope.Law native
      (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before)) :
    Prefix hashv H (SdkC_BatchSource.currentCode hashv proof p root) before native.2.2 :=
  BEj_LocalExport.attempted call hashv binding sha256 H p1 syscall _ 900
    (GExq_BatchBudget.current hashv proof p root) state before native law

/-- Resumed batch retains its own physical recorder cut; intervening
checkpoint/adversary calls are not silently erased or assumed absent. -/
theorem stage {S E : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Digest)
    (state : S) (before : Log) (native : BEh_Scope.Outcome S Unit E)
    (law : BEh_Scope.Law native
      (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before)) :
    Prefix hashv H (SdkC_BatchSource.stageCode hashv proof p root) before native.2.2 :=
  BEj_LocalExport.attempted call hashv binding sha256 H p1 syscall _ 900
    (GExq_BatchBudget.stage hashv proof p root) state before native law

#print axioms current
#print axioms stage
end AspisR1.BEj_SlotExport
end
