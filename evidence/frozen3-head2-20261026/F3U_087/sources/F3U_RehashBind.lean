import F3U_Rehash
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_RehashBind
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode

theorem bind {A B : Type} (H : Bytes → State) (p : Code A) (k : A → Code B) :
    F3U_Rehash.code H (p >>= k)=F3U_Rehash.code H p >>= (fun value=>F3U_Rehash.code H (k value)) := by
  induction p with
  | done value=>rfl
  | step result next ih=>exact congrArg (Code.step result) (funext ih)
  | digest D hash parts next ih=>exact congrArg (Code.digest (F3U_Rehash.dictionary H D) hash parts) (funext ih)

theorem lift {A : Type} (H : Bytes → State) (r : Result A) :
    F3U_Rehash.code H (monadLift r : Code A)=monadLift r := rfl

theorem digest {Hash : Type} (H : Bytes → State) (D : AspisR1PublicPreparation.aspis_core.Digest32 Hash)
    (hash : Hash) (parts : Slice (Slice U8)) :
    F3U_Rehash.code H (effects.digest D hash parts)=effects.digest (F3U_Rehash.dictionary H D) hash parts := rfl

#print axioms bind
#print axioms lift
#print axioms digest
end AspisR1.F3U_RehashBind
end
