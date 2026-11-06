import NKK_LogClauses
set_option autoImplicit false
namespace NKK_Invoke
open Aeneas Aeneas.Std

/-- A continuation receives the returned value of this exact call. Its domain
is required only on the actual Ok branch; arbitrary replies are not silently
promoted to caller invariants. -/
theorem bind {E A B : Type} (p : E → Prop) (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) (first : NKK_LogClauses.Holds p m)
 (next : ∀ a,m.result=.ok a → NKK_LogClauses.Holds p (k a)) :
 NKK_LogClauses.Holds p (m >>= k) := by
 cases m with
 | mk result events =>
  cases result with
  | fail err => exact first
  | div => exact first
  | ok a => exact List.forall_append.mpr ⟨first,next a rfl⟩

/-- No suffix at an aborting call in the actual source invocation. -/
theorem abort {E A B : Type} (m : NJU_Log.Run E A) (k : A → NJU_Log.Run E B)
 (err : Error) (stopped : m.result=.fail err) :
 (m >>= k).events=m.events ∧ (m >>= k).result=.fail err := by
 have h:=NJU_Log.fail_prefix m err stopped k
 exact ⟨h.2,h.1⟩

theorem diverges {E A B : Type} (m : NJU_Log.Run E A) (k : A → NJU_Log.Run E B)
 (stopped : m.result=.div) :
 (m >>= k).events=m.events ∧ (m >>= k).result=.div := by
 have h:=NJU_Log.div_prefix m stopped k
 exact ⟨h.2,h.1⟩

#print axioms bind
#print axioms abort
#print axioms diverges
end NKK_Invoke
