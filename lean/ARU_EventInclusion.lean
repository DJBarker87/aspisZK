import ARU_Issued
import P6C_EventTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_EventInclusion
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem inclusion {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (bad : List (Bytes × State) → A → Prop)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    P6C_EventTransport.realEvent hashv code bad → P6C_EventTransport.idealEvent H code bad := by
  rintro ⟨value,accepted,failure⟩
  have same := ARS_QueryTransport.accepted hashv H code value accepted agrees
  exact ⟨value,by rw [same],by simpa only [same] using failure⟩

#print axioms inclusion
end AspisR1.ARU_EventInclusion
end
