import NKK_FieldFold
set_option autoImplicit false
noncomputable section
namespace NKK_FieldShape
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold

def tag : Value → Kind | .k _=>.k | .e _=>.e

theorem call_tag (kind : Kind) (r next : Reader) (value : Value)
 (returned : response (event kind r)=ok (.Ok value,next)) : tag value=kind := by
 cases kind with
 | k =>
  cases call : NIL_FreshOps.readK r with
  | fail err => simp only [event,response,mapOuter,call] at returned;cases returned
  | div => simp only [event,response,mapOuter,call] at returned;cases returned
  | ok pair =>
   rcases pair with ⟨inner,last⟩
   cases inner with
   | Err err => simp only [event,response,mapOuter,mapInner,call] at returned;cases returned
   | Ok q => simp only [event,response,mapOuter,mapInner,call] at returned;cases returned;rfl
 | e =>
  cases call : NIL_FreshOps.readE r with
  | fail err => simp only [event,response,mapOuter,call] at returned;cases returned
  | div => simp only [event,response,mapOuter,call] at returned;cases returned
  | ok pair =>
   rcases pair with ⟨inner,last⟩
   cases inner with
   | Err err => simp only [event,response,mapOuter,mapInner,call] at returned;cases returned
   | Ok q => simp only [event,response,mapOuter,mapInner,call] at returned;cases returned;rfl

theorem shape (kinds : List Kind) (r last : Reader) (values : List Value)
 (returned : (program kinds r).result=ok (.Ok (values,last))) :
 values.map tag=kinds := by
 induction kinds generalizing r last values with
 | nil => cases returned;rfl
 | cons kind kinds ih =>
  cases call : response (event kind r) with
  | fail err =>
   simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call] at returned
   cases returned
  | div =>
   simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call] at returned
   cases returned
  | ok pair =>
   rcases pair with ⟨inner,next⟩
   cases inner with
   | Err err =>
    simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call] at returned
    cases returned
   | Ok value =>
    have head:=call_tag kind r next value call
    cases tail : (program kinds next).result with
    | fail err =>
     simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call,tail] at returned
     cases returned
    | div =>
     simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call,tail] at returned
     cases returned
    | ok inner =>
     cases inner with
     | Err err =>
      simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call,tail,mapInner] at returned
      cases returned
     | Ok pair =>
      rcases pair with ⟨rest,after⟩
      have restShape:=ih next after rest tail
      simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,NKK_FieldFold.call,call,tail,mapInner] at returned
      cases returned
      simpa only [List.map_cons,head,restShape]

#print axioms call_tag
#print axioms shape
end NKK_FieldShape
