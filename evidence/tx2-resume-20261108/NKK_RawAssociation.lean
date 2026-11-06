import NKK_RunEval
set_option autoImplicit false
noncomputable section
namespace NKK_RawFold
open Aeneas Aeneas.Std Result NKK_NativeRaw

/-- Prefix induction for the actual source-ordered raw log. No independent
native/source stream, endpoint or successful-child premise is supplied. -/
theorem association (n : Usize) (count : Nat) (r : Reader)
 (before : List (Array U8 n)) :
 Matches before
 (fold (observed n count r).events ⟨before,r,.ok ()⟩)
 (observed n count r).result := by
 induction count generalizing r before with
 | zero => simp only [NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,observed,Matches,fold,NJU_Log.bind,List.append_nil,List.foldl_nil]
 | succ count ih =>
  cases call : NJC_ConcreteUnwrap.raw n r with
  | fail err =>
   simp only [NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,observed,NJU_Log.record,NJU_Log.bind,call,Matches,fold,
    List.foldl_cons,List.foldl_nil,step]
  | div =>
   simp only [NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,observed,NJU_Log.record,NJU_Log.bind,call,Matches,fold,
    List.foldl_cons,List.foldl_nil,step]
  | ok pair =>
   rcases pair with ⟨b,next⟩
   have tail := ih next (before++[b])
   cases rest : (observed n count next).result with
   | fail err =>
    simpa only [NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,observed,NJU_Log.record,NJU_Log.bind,call,rest,Matches,fold,
     List.singleton_append,List.foldl_cons,step] using tail
   | div =>
    simpa only [NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,observed,NJU_Log.record,NJU_Log.bind,call,rest,Matches,fold,
     List.singleton_append,List.foldl_cons,step] using tail
   | ok out =>
    rcases out with ⟨bs,last⟩
    simpa only [NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,observed,NJU_Log.record,NJU_Log.bind,call,rest,Matches,fold,
     List.singleton_append,List.foldl_cons,step,List.append_assoc,List.singleton_append,List.append_nil] using tail

#print axioms association
end NKK_RawFold
