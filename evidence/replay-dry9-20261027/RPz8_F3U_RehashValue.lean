import RPz7_F3U_Rehash
import F3U_ReifyValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_RehashValue
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation.PreparedHashCode

theorem value {A : Type} (H : Bytes → State) (p : Code A) :
    (eval H (oracleProgram p)).2=erase (F3U_Rehash.code H p) := by
  rw [←SdkD_PrepareLower.program,F3U_ReifyValue.value,←F3U_Rehash.lowered H p]
  exact SdkD_PrepareLower.erasure _ _ (F3U_Rehash.associated H p)

#print axioms value
end AspisR1.F3U_RehashValue
end
