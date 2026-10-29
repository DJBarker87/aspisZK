import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_PushPrefix
open PV_OWNC_Vector PV_OWNC_PushFold PV_OWN_View
/-- Every later append leaves the earlier initialized logical value intact. -/
theorem retained {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (i : Nat) (hi:i<b.length) : (append k b xs).values i=b.values i := by
 induction xs generalizing b with
 | nil => rfl
 | cons v vs ih =>
  rw [append,ih]
  · simp only [push,show i≠b.length by omega,ite_false]
  · change i<b.length+1
    omega
#print axioms retained
end R1Z.PV_OWND_PushPrefix
