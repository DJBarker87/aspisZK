import NKE_Free
set_option autoImplicit false
namespace NKE_RunExt

theorem bind {E A B : Type} (m : NJU_Log.Run E A) (first second : A → NJU_Log.Run E B)
 (same : ∀ value,first value=second value) : (m >>= first)=(m >>= second) :=
 congrArg (fun continuation=>m >>= continuation) (funext same)
#print axioms bind
end NKE_RunExt
