import NJU_Log
set_option autoImplicit false
namespace NLM_LogLaws
open Aeneas Aeneas.Std
/-- Chronology, including the error prefix, composes without discarding
callee effects. This is the algebra used by the snapshot site fold. -/
theorem assoc {E A B C : Type} (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) (l : B → NJU_Log.Run E C) :
 NJU_Log.bind (NJU_Log.bind m k) l=NJU_Log.bind m (fun a=>NJU_Log.bind (k a) l) := by
 cases h : m.result with
 | fail err => simp only [NJU_Log.bind,h]
 | div => simp only [NJU_Log.bind,h]
 | ok a =>
   cases hk : (k a).result <;> simp only [NJU_Log.bind,h,hk,List.append_assoc]
#print assoc
#print axioms assoc
end NLM_LogLaws
