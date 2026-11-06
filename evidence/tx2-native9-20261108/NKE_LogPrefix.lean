import NJU_Log
set_option autoImplicit false
namespace NKE_LogPrefix
open Aeneas Aeneas.Std
/-- Prefix fold preserves the complete event carrier; no rejected suffix is added. -/
def G {E S : Type} (step : S → E → S) (state : S) (log : List E) : S :=
 log.foldl step state

theorem append {E S : Type} (step : S → E → S) (state : S) (pre tail : List E) :
 G step state (pre ++ tail)=G step (G step state pre) tail := by
 simp only [G,List.foldl_append]

/-- The induction obligation is per actual event and per arbitrary pre-state.
A concrete native parent must instantiate stepLaw; this theorem alone is no credit. -/
theorem prefixes {E S T : Type} (native : S → E → S) (source : T → E → T)
 (port : S → T) (stepLaw : ∀ state event,port (native state event)=source (port state) event)
 (state : S) (log : List E) : port (G native state log)=G source (port state) log := by
 induction log generalizing state with
 | nil => rfl
 | cons event tail ih =>
  change port (G native (native state event) tail)=G source (source (port state) event) tail
  rw [ih,stepLaw]

theorem abort {E A B S : Type} (step : S → E → S) (state : S)
 (m : NJU_Log.Run E A) (err : Error) (failed : m.result=.fail err)
 (tail : A → NJU_Log.Run E B) :
 G step state (m >>= tail).events=G step state m.events := by
 rw [(NJU_Log.fail_prefix m err failed tail).2]

theorem diverge {E A B S : Type} (step : S → E → S) (state : S)
 (m : NJU_Log.Run E A) (failed : m.result=.div)
 (tail : A → NJU_Log.Run E B) :
 G step state (m >>= tail).events=G step state m.events := by
 rw [(NJU_Log.div_prefix m failed tail).2]
#print axioms append
#print axioms prefixes
#print axioms abort
#print axioms diverge
end NKE_LogPrefix
