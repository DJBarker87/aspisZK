import F3U_Oracle
import SdkD_PrepareLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Rehash
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode

def dictionary (H : Bytes → State) {Hash : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 Hash) :
    AspisR1PublicPreparation.aspis_core.Digest32 Hash :=
  {D with digest:=fun _ parts=>F3U_Oracle.hashv H parts}

def code {A : Type} (H : Bytes → State) : Code A → Code A
  | .done value=>.done value
  | .step result next=>.step result (fun value=>code H (next value))
  | .digest D hash parts next=>.digest (dictionary H D) hash parts (fun value=>code H (next value))

theorem lowered {A : Type} (H : Bytes → State) (p : Code A) :
    SdkD_PrepareLower.lower (code H p)=SdkD_PrepareLower.lower p := by
  induction p with
  | done value=>rfl
  | step result next ih=>exact congrArg (CheckpointBytes5Effect.Code.step result) (funext ih)
  | digest D hash parts next ih=>exact congrArg (CheckpointBytes5Effect.Code.read parts) (funext ih)

theorem associated {A : Type} (H : Bytes → State) (p : Code A) :
    SdkD_PrepareLower.Associated (F3U_Oracle.hashv H) (code H p) := by
  induction p with
  | done value=>trivial
  | step result next ih=>cases result with
    | ok value=>exact ih value
    | fail e=>trivial
    | div=>trivial
  | digest D hash parts next ih=>exact ⟨rfl,ih⟩

#print axioms lowered
#print axioms associated
end AspisR1.F3U_Rehash
end
