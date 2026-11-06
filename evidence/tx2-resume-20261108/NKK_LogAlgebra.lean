import NKK_RunEval
set_option autoImplicit false
namespace NKK_LogAlgebra
open Aeneas Aeneas.Std

theorem bind_congr {E A B : Type} (m : NJU_Log.Run E A)
 (left right : A → NJU_Log.Run E B) (same : ∀ a,left a=right a) :
 (m >>= left)=(m >>= right) := congrArg (fun k=>m >>= k) (funext same)

theorem bind_assoc {E A B C : Type} (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) (next : B → NJU_Log.Run E C) :
 ((m >>= k) >>= next)=(m >>= fun a=>k a >>= next) := by
 cases m with
 | mk result events =>
  cases result with
  | fail err => rfl
  | div => rfl
  | ok a =>
   cases h : (k a).result with
   | fail err => simp only [NKK_RunEval.bind_eq,NJU_Log.bind,h]
   | div => simp only [NKK_RunEval.bind_eq,NJU_Log.bind,h]
   | ok b =>
    simp only [NKK_RunEval.bind_eq,NJU_Log.bind,h,List.append_assoc]

#print axioms bind_congr
#print axioms bind_assoc
end NKK_LogAlgebra
