import NLQ_SnapshotFold
set_option autoImplicit false
namespace NLQ_LogPrefix
open Aeneas Aeneas.Std Result
/-- Preserve the completed prefix's entire event list before the next action;
failed/divergent actions keep their attempted events and suppress the suffix. -/
theorem next {E A B : Type} (h : NJU_Log.Run E A) (a : A)
 (reply : h.result=.ok a) (k : A → NJU_Log.Run E B) :
 NJU_Log.bind h k = ⟨(k a).result,h.events++(k a).events⟩ := by
 simp only [NJU_Log.bind,reply]
theorem fail {E A B : Type} (h : NJU_Log.Run E A) (e : Error)
 (reply : h.result=.fail e) (k : A → NJU_Log.Run E B) :
 NJU_Log.bind h k = ⟨.fail e,h.events⟩ := by
 simp only [NJU_Log.bind,reply]
theorem div {E A B : Type} (h : NJU_Log.Run E A)
 (reply : h.result=.div) (k : A → NJU_Log.Run E B) :
 NJU_Log.bind h k = ⟨.div,h.events⟩ := by
 simp only [NJU_Log.bind,reply]
#print axioms next
#print axioms fail
#print axioms div
end NLQ_LogPrefix
