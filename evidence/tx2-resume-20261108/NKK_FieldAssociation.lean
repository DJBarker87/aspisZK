import NKK_FieldFold
set_option autoImplicit false
noncomputable section
namespace NKK_FieldFold
open Aeneas Aeneas.Std Result

/-- Induction over the actual mixed E/K source log, on arbitrary pre-state.
Every Ok, Rust Err, abort and divergence uses the SAME event and arguments. -/
theorem association (kinds : List Kind) (r : Reader) (before : List Value) :
 Matches before (fold (program kinds r).events ⟨before,r,.ok (.Ok ())⟩)
 (program kinds r).result := by
 induction kinds generalizing r before with
 | nil => simp only [program,NKK_RunEval.pure_eq,Matches,fold,List.foldl_nil,List.append_nil]
 | cons kind kinds ih =>
  cases reply : response (event kind r) with
  | fail err =>
   simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,reply,Matches,fold,List.foldl_cons,List.foldl_nil,step]
  | div =>
   simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,reply,Matches,fold,List.foldl_cons,List.foldl_nil,step]
  | ok pair =>
   rcases pair with ⟨inner,next⟩
   cases inner with
   | Err err =>
    simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,reply,Matches,fold,List.foldl_cons,List.foldl_nil,List.append_nil,step]
   | Ok value =>
    have tail:=ih next (before++[value])
    cases rest : (program kinds next).result with
    | fail err =>
     simpa only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,reply,rest,Matches,fold,List.singleton_append,List.foldl_cons,step] using tail
    | div =>
     simpa only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,reply,rest,Matches,fold,List.singleton_append,List.foldl_cons,step] using tail
    | ok inner =>
     cases inner with
     | Err err =>
      simpa only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,reply,rest,Matches,fold,List.singleton_append,List.foldl_cons,step,mapInner,List.append_nil] using tail
     | Ok pair =>
      rcases pair with ⟨values,last⟩
      simpa only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,reply,rest,Matches,fold,List.singleton_append,List.foldl_cons,step,mapInner,List.append_nil,List.append_assoc] using tail

#print axioms association
end NKK_FieldFold
