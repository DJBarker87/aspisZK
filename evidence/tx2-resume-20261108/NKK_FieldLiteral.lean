import NKK_FieldFold
import NKK_LogAlgebra
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_FieldLiteral
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold

theorem call_k (r : Reader) : call .k r=
 (do let (reply,next) ← NJU_ResumeObserved.recordK r
     pure (mapInner Value.k reply,next)) := by
 cases run : NIL_FreshOps.readK r with
 | fail err => simp only [call,event,response,mapOuter,run,NJU_ResumeObserved.recordK,NJU_Log.record,
   NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,List.append_nil]
 | div => simp only [call,event,response,mapOuter,run,NJU_ResumeObserved.recordK,NJU_Log.record,
   NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,List.append_nil]
 | ok pair =>
  rcases pair with ⟨reply,next⟩
  simp only [call,event,response,mapOuter,run,NJU_ResumeObserved.recordK,NJU_Log.record,
   NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,List.append_nil]

theorem call_e (r : Reader) : call .e r=
 (do let (reply,next) ← NJU_ResumeObserved.recordE r
     pure (mapInner Value.e reply,next)) := by
 cases run : NIL_FreshOps.readE r with
 | fail err => simp only [call,event,response,mapOuter,run,NJU_ResumeObserved.recordE,NJU_Log.record,
   NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,List.append_nil]
 | div => simp only [call,event,response,mapOuter,run,NJU_ResumeObserved.recordE,NJU_Log.record,
   NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,List.append_nil]
 | ok pair =>
  rcases pair with ⟨reply,next⟩
  simp only [call,event,response,mapOuter,run,NJU_ResumeObserved.recordE,NJU_Log.record,
   NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,List.append_nil]

def literal : List Kind → Reader → NJU_Log.Run NJU_ResumeObserved.Event
 (core.result.Result (List Value × Reader) verifier.Error)
 | [],r => pure (.Ok ([],r))
 | .k::kinds,r => do
   let (reply,next) ← NJU_ResumeObserved.recordK r
   match reply with
   | .Err err => pure (.Err err)
   | .Ok value =>
     let tail ← literal kinds next
     pure (mapInner (fun x=>(Value.k value::x.1,x.2)) tail)
 | .e::kinds,r => do
   let (reply,next) ← NJU_ResumeObserved.recordE r
   match reply with
   | .Err err => pure (.Err err)
   | .Ok value =>
     let tail ← literal kinds next
     pure (mapInner (fun x=>(Value.e value::x.1,x.2)) tail)

theorem source (kinds : List Kind) (r : Reader) : program kinds r=literal kinds r := by
 induction kinds generalizing r with
 | nil => rfl
 | cons kind kinds ih =>
  cases kind with
  | k =>
   unfold program
   rw [call_k]
   simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind]
   unfold literal
   apply NKK_LogAlgebra.bind_congr
   rintro ⟨reply,next⟩
   cases reply with
   | Err err => rfl
   | Ok value => rw [ih];rfl
  | e =>
   unfold program
   rw [call_e]
   simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind]
   unfold literal
   apply NKK_LogAlgebra.bind_congr
   rintro ⟨reply,next⟩
   cases reply with
   | Err err => rfl
   | Ok value => rw [ih];rfl

#print axioms call_k
#print axioms call_e
#print axioms source
end NKK_FieldLiteral
