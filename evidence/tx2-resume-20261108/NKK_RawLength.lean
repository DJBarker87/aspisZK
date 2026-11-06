import NKK_RunEval
set_option autoImplicit false
noncomputable section
namespace NKK_RawFold
open Aeneas Aeneas.Std Result NKK_NativeRaw

theorem length (n : Usize) (count : Nat) (r : Reader)
 (bs : List (Array U8 n)) (last : Reader)
 (returned : (observed n count r).result=.ok (bs,last)) : bs.length=count := by
 induction count generalizing r bs last with
 | zero => cases returned;rfl
 | succ count ih =>
  cases call : NJC_ConcreteUnwrap.raw n r with
  | fail err =>
   simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
    NJU_Log.record,NJU_Log.bind,call] at returned
   cases returned
  | div =>
   simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
    NJU_Log.record,NJU_Log.bind,call] at returned
   cases returned
  | ok pair =>
   rcases pair with ⟨b,next⟩
   cases rest : (observed n count next).result with
   | fail err =>
    simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
     NJU_Log.record,NJU_Log.bind,call,rest] at returned
    cases returned
   | div =>
    simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
     NJU_Log.record,NJU_Log.bind,call,rest] at returned
    cases returned
   | ok pair =>
    rcases pair with ⟨tail,after⟩
    simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
     NJU_Log.record,NJU_Log.bind,call,rest] at returned
    have countEq:=ih next tail after rest
    cases returned
    simpa only [List.length_cons] using congrArg Nat.succ countEq

#print axioms length
end NKK_RawFold
