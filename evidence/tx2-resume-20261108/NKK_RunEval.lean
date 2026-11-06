import NKK_RawFold
set_option autoImplicit false
namespace NKK_RunEval
open Aeneas Aeneas.Std

theorem bind_eq {E A B : Type} (m : NJU_Log.Run E A) (k : A → NJU_Log.Run E B) :
 (m >>= k)=NJU_Log.bind m k := rfl

theorem pure_eq {E A : Type} (a : A) :
 (pure a : NJU_Log.Run E A)=⟨.ok a,[]⟩ := rfl

#print axioms bind_eq
#print axioms pure_eq
end NKK_RunEval
