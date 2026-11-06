import NKK_ClausesQueryEnd
set_option autoImplicit false
namespace NKK_LogReduce
open Aeneas Aeneas.Std

theorem pure_bind {E A B : Type} (a : A) (k : A → NJU_Log.Run E B) :
 ((pure a : NJU_Log.Run E A) >>= k)=k a := rfl

theorem lift_ok_bind {E A B : Type} (a : A) (k : A → NJU_Log.Run E B) :
 ((monadLift (Result.ok a) : NJU_Log.Run E A) >>= k)=k a := rfl

theorem liftM_ok_bind {E A B : Type} (a : A) (k : A → NJU_Log.Run E B) :
 ((liftM (Result.ok a) : NJU_Log.Run E A) >>= k)=k a := rfl

#print axioms pure_bind
#print axioms lift_ok_bind
#print axioms liftM_ok_bind
end NKK_LogReduce
