import RPz8_ART_AcceptedBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_WrapperAccepted
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem exact {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A)
    (accepted : (eval H (ART_PartialAccount.wrapper hashv code)).2 = ok value) :
    eval H (ART_PartialAccount.wrapper hashv code) = eval H (SdkC_Oracle.program code) := by
  have raw : (eval H (ART_PartialProgram.program hashv code [])).2.1 = ok value := by
    simpa only [ART_PartialAccount.wrapper,eval_bind,eval] using accepted
  rw [ART_AcceptedBridge.source hashv H code [] value raw]
  simp only [ART_PartialAccount.wrapper,eval_bind,eval,List.append_nil,raw]

#print axioms exact
end AspisR1.ART_WrapperAccepted
end
