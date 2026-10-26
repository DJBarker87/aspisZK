import ART_PartialAccount
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_WrapperExact
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem execution {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    eval H (ART_PartialAccount.wrapper hashv code) =
      (ART_PartialProgram.attempted H (run hashv code []).2,(run hashv code []).1) := by
  simp only [ART_PartialAccount.wrapper,eval_bind,ART_PartialExact.execution hashv H code agrees,
    eval,List.append_nil]

#print axioms execution
end AspisR1.ART_WrapperExact
end
