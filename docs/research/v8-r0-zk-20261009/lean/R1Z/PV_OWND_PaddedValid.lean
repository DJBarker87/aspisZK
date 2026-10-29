import R1Z.PV_OWND_PaddedFold
set_option autoImplicit false
namespace R1Z.PV_OWND_PaddedValid
open PV_OWNC_Vector PV_OWN_View PV_OWN_Bytes PV_OWND_PaddedFold

theorem valid {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j : Nat)
 (h:Valid k b) (room:b.length+xs.length≤b.capacity)
 (bounded:∀ v i z, k.encode v i=some z → i<k.width)
 (agrees:∀ i v, PV_OWNB_Padding.Agrees (k.encode v) (payload i v)) :
 Valid k (append k b xs payload j) := by
 induction xs generalizing b j with
 | nil => exact h
 | cons v vs ih =>
  apply ih
  · exact PV_OWNC_PushValid.valid k b v _ h (by simp only [List.length_cons] at room;omega)
     bounded (agrees j v)
  · change b.length+1+vs.length≤b.capacity
    simp only [List.length_cons] at room
    omega
#print axioms valid
end R1Z.PV_OWND_PaddedValid
