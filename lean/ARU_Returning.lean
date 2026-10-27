import ARU_OracleLog
import P6C_Pair
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Returning
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem returning {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A) (accepted : (run hashv code []).1 = ok value)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    SdkC_BatchPair.Returning hashv H code value := by
  have same := ARS_QueryTransport.accepted hashv H code value accepted agrees
  refine ⟨accepted,same,?_⟩
  intro a d bad member
  have logs := congrArg Prod.fst same
  dsimp only at logs
  rw [←logs] at member
  exact bad (ARU_OracleLog.coherent H _ _ member)

theorem safe {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A) (accepted : (run hashv code []).1 = ok value)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    P6C_Pair.Safe hashv H code value :=
  P6C_Pair.safe hashv H code value (returning hashv H code value accepted agrees)

#print axioms returning
#print axioms safe
end AspisR1.ARU_Returning
end
